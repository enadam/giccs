#!/usr/bin/python3
#
# INDEXER: {{{
# --index
# --indexer
# --indexer-format
#
# COMPRESS:
# --uncompressed-index
# --index-compressor
# --index-decompressor
#
# ENCRYPT:
# --no-encrypt, --no-decrypt
# --encryption-command
# --decryption-command
# --encryption-key
# --encryption-key-command
# --no-header
# --no-verify-blob-size
# --cleatext-index
#
# UPLOAD/DOWNLOAD:
# --reupload
# --upload-chunk-size
# --progress
# --timeout
#
# upload
#	INDEXER, COMPRESS, ENCRYPT, UPLOAD
# download
#	COMPRESS, ENCRYPT, DOWNLOAD
# index upload
#	INDEXER, COMPRESS, ENCRYPT, UPLOAD
# index list
# index get
#	COMPRESS, ENCRYPT, DOWNLOAD
# index delete
# }}}
#
# TODO: {{{
# rename Cipher/Encrypt/Decrypt to Internal*
# fix delete local/remote --uuid -x
# store file list in buckets
# upload/download: split plan and execution
# consider using clone sources when uploading
# find a better name and update CONFIG_FILE and $BTRFS_BACKUP_ARCHIVE_CONFIG
#	(barbie? giccs?)
# error handing for UUID, base64, shlex, json
# better top-level exception handling (--debug)
#
# list remote: show mtime
# consistency check of remote backups
# encrypt blob name, UUIDs?
#
# document required permissions
#   * storage.objects.create
#   * storage.objects.update (for patch())
#   * storage.buckets.list (for list buckets)
#   * storage.objects.list
#   * storage.objects.get
# document the use of gpg-agent
#
# protect against:
#   * blob swapping: header
#   * block swapping between blobs: header
#   * block reordering: random sequence number
#   * blob truncation: expected number of blocks
# }}}

from typing import	TypeVar, Final, Protocol, \
			Any, Union, Optional, \
			Generator, Iterable, Callable, \
			Container, Collection, Sequence, \
			BinaryIO, Dict, List, Tuple, ByteString

import sys, os, fcntl
import subprocess, io
import time, datetime
import re, bisect
import base64, uuid, shlex
import random, secrets
import dataclasses, struct
import argparse, configparser

import btrfs

import google.cloud.storage
import google.oauth2.service_account

UUID0 = uuid.UUID(int=0)

CONFIG_FILE = "btrfs-backup-archive.conf"

DFLT_COMPRESSION = "xz"
DFLT_COMPRESSOR = (DFLT_COMPRESSION, "-c")
DFLT_DECOMPRESSOR = (DFLT_COMPRESSION, "-dc")

# btrfs constants and structures {{{
# We store btrfs volume UUIDs in uuid.UUID, so it's important that they
# have the same size.
BTRFS_UUID_SIZE = 16
assert len(UUID0.bytes) == BTRFS_UUID_SIZE

BTRFS_VOL_NAME_MAX = 255
btrfs_ioctl_get_subvol_info_args_st = struct.Struct(
	"=Q%dsQQQQ" % (BTRFS_VOL_NAME_MAX + 1)
	+ ("%ds" % BTRFS_UUID_SIZE) * 3
	+ "4Q"
	+ "QI4x" * 4
	+ "8Q")
BTRFS_IOC_GET_SUBVOL_INFO = btrfs.ioctl._IOR(
				btrfs.ioctl.BTRFS_IOCTL_MAGIC, 60,
				btrfs_ioctl_get_subvol_info_args_st)

BTRFS_SUBVOL_NAME_MAX = 4039
btrfs_ioctl_vol_args_v2_st = struct.Struct(
	"="
	+ "8x" * 3
	+ "8x" * 4
	+ "%ds" % (BTRFS_SUBVOL_NAME_MAX + 1))
BTRFS_IOC_SNAP_DESTROY_V2 = btrfs.ioctl._IOW(
				btrfs.ioctl.BTRFS_IOCTL_MAGIC, 63,
				btrfs_ioctl_vol_args_v2_st)
# }}}

class UserError(Exception): pass
class FatalError(Exception): pass
class SecurityError(FatalError): pass
class ConsistencyError(FatalError): pass

# A configparser.ConfigParser with extra functionality.
class ConfigParser(configparser.ConfigParser): # {{{
	# Type of option values in the default section.  Used by is_default().
	class Default(str): pass

	class Interpol(configparser.BasicInterpolation):
		def before_get(self, parser, section, option, value, defaults):
			# Preserve the type of @value.
			ret = super().before_get(
					parser, section, option, value,
					defaults)
			return type(value)(ret) if value is not None else None

	def __init__(self, *args, **kw):
		self.filenames = [ ]
		return super().__init__(
			*args,
			delimiters=('=',),
			comment_prefixes=('#',),
			interpolation=self.Interpol(),
			default_section='default',
			allow_no_value=True,
			**kw)

	def optionxform(self, key):
		return key.replace('-', '_')

	def read(self, *args, **kw):
		ret = super().read(*args, **kw)
		if ret:	# Convert @defaults to Default:s.
			defaults = self.defaults()
			for key, val in defaults.items():
				defaults[key] = self.Default(val)
			self.filenames += ret
		return ret

	def is_default(self, value) -> bool:
		return isinstance(value, self.Default)

	def as_dict(self, section: str) -> Dict[str, str]:
		return dict(self.items(section))
# }}}

@dataclasses.dataclass
class Snapshot: # {{{
	# The expected format of snapshot directories (YYYY-MM-DD[.SEQ][_TAG]).
	fname_re = re.compile(r"^(\d{4}-\d{2}-\d{2})(?:\.(\d+))?(?:_(.*))?$")

	fname:	str
	uuid:	uuid.UUID
	date:	str = dataclasses.field(init=False)
	seq:	Optional[int] = dataclasses.field(init=False)
	tag:	Optional[str] = dataclasses.field(init=False)

	# Allow these fields to be overwritten at the class level
	# because they are influenced by the command line options.
	include_uuid_in_fmt: bool = dataclasses.field(init=False,
							default=False)
	emphasize_uuid_in_fmt: bool = dataclasses.field(init=False,
							default=False)

	@classmethod
	def parse(self, fname: str) -> Optional[re.Match]:
		return self.fname_re.fullmatch(fname)

	# Parse @self.fname into @self.date, @self.seq and @self.tag.
	def __post_init__(self):
		m = self.parse(self.fname)
		if m is None:
			raise FatalError(f"{self.fname}: invalid fname")

		self.date = m.group(1)
		self.seq = int(m.group(2)) if m.group(2) is not None else None
		self.tag = m.group(3)

	def matches(self, what: Union[str, uuid.UUID]) -> bool:
		if isinstance(what, uuid.UUID):
			return self.uuid == what
		else:
			return self.fname == what

	def __str__(self):
		if not self.include_uuid_in_fmt:
			return self.fname
		elif not self.emphasize_uuid_in_fmt:
			return "%s (%s)" % (self.fname, self.uuid)
		else:	# Make the UUID bold.
			return "%s (%s%s%s)" % (
					self.fname,
					"\x1b[1m",
					self.uuid,
					"\x1b[0m")

	def __eq__(self, other):
		return self.uuid == other.uuid

	# Operator for sorting.  @other must be different from @self
	# as an additional measure for consistency.
	def __lt__(self, other):
		if self.date < other.date:
			return True
		elif self.date > other.date:
			return False
		elif self.seq is None and other.seq is None:
			raise ConsistencyError(
				f"{self.fname} and {other.fname} "
				"have the same date")
		elif self.seq is None:
			return True
		elif other.seq is None:
			return False
		elif self.seq == other.seq:
			raise ConsistencyError(
				f"{self.fname} and {other.fname} "
				"have the same date and seq")
		else:
			return self.seq < other.seq
# }}}

@dataclasses.dataclass
class Backup(Snapshot): # {{{
	# A local snapshot may have a @full and/or a @delta backup
	# on the top of a @prev:ious backup.
	full:	Optional[google.cloud.storage.Blob] = None
	delta:	Optional[google.cloud.storage.Blob] = None
	prev:	Optional[uuid.UUID] = dataclasses.field(init=False)

	# Used by backup_restorable().
	restorable: Optional[bool] = None

	def __post_init__(self):
		super().__post_init__()
		assert self.full is not None or self.delta is not None

		self.prev = None
		if self.delta is not None:
			self.set_prev(self.delta)

	def set_full(self, blob: google.cloud.storage.Blob) -> None:
		assert self.full is None
		self.full = blob

	def set_delta(self, blob: google.cloud.storage.Blob) -> None:
		assert self.delta is None
		self.delta = blob
		self.set_prev(self.delta)

	def set_prev(self, blob: google.cloud.storage.Blob) -> None:
		assert self.prev is None
		if "prev" not in blob.metadata:
			raise ConsistencyError(
				f"{blob.name} has no \"prev\" metadata")
		self.prev = uuid.UUID(blob.metadata["prev"])
# }}}

# The internal encryption and decryption classes.
class Cipher: # {{{
	# Define the interface of the underlying @cipher we'll use
	# rather than naming the concrete class, so we can defer importing
	# the cryptography module until it's needed (if needed at all).
	class Primitive(Protocol):
		def encrypt(self, nonce: ByteString, data: bytes,
				associated_data: Optional[bytes]) -> bytes:
			...

		def decrypt(self, nonce: ByteString, data: bytes,
				associated_data: Optional[bytes]) -> bytes:
			...

	# Header included with each block of ciphertext consisting of:
	#   1) UUIDs unambiguously identifying the Backup it belongs to
	#   2) a pseudo-random sequence number unique for each ciphertext;
	#      the first block contains the seed, from which the sequence
	#      number of the remaining blocks are derived.
	#
	# 1) protects against swapping ciphertext blocks between Backups
	# (or swapping entire Backups with each other) while 2) prevents
	# the reordering of blocks within a Backup.
	#
	# Calculating a MAC for the whole Backup would be less secure because
	# this way we can detect tampering as soon as possible, before piping
	# data to btrfs receive, which only operates reliably and securely if
	# the input is trustworthy.
	partial_header_st: Final[struct.Struct] = struct.Struct("=Q")
	header_st: Final[struct.Struct] = \
		struct.Struct("=" + ("%ds" % BTRFS_UUID_SIZE) * 2 + "Q")

	NONCE_SIZE: Final[int]		= 12
	RND_BITS: Final[int]		= 64
	TAG_SIZE: Final[int]		= 16

	# AESGCM has been measured to be the fastest with this block size.
	OUTPUT_SIZE: Final[int]		= 512 * 1024
	CIPHERTEXT_SIZE: Final[int]	= OUTPUT_SIZE - NONCE_SIZE
	CLEARTEXT_SIZE: Final[int]	= CIPHERTEXT_SIZE - TAG_SIZE
	INPUT_SIZE: Final[int]		= CLEARTEXT_SIZE - header_st.size

	key: bytes
	cipher: Primitive
	wrapped: Optional[BinaryIO]

	this_uuid: Optional[uuid.UUID]
	this_uuid_bytes: bytes

	parent_uuid: Optional[uuid.UUID]
	parent_uuid_bytes: bytes

	def __init__(self, key: bytes, wrapped: Optional[BinaryIO],
			this_uuid: Optional[uuid.UUID] = None,
			parent_uuid: Optional[uuid.UUID] = None):
		from cryptography.hazmat.primitives.ciphers import aead

		self.key = key
		self.cipher = aead.AESGCM(key)
		self.wrapped = wrapped

		self.this_uuid = this_uuid
		self.this_uuid_bytes = ensure_uuid(this_uuid).bytes

		assert this_uuid is not None or parent_uuid is None
		self.parent_uuid = parent_uuid
		self.parent_uuid_bytes = ensure_uuid(parent_uuid).bytes

	def init(self, wrapped: Optional[BinaryIO]) -> None:
		assert self.wrapped is None
		self.wrapped = wrapped

	def mkprng(self, seed: int) -> random.Random:
		prng = random.Random()
		prng.seed(seed, version=2)
		return prng

class Encrypt(Cipher):
	class CSRNG(random.Random):
		def getrandbits(self, n: int) -> int:
			return secrets.randbits(n)

		def randbytes(self, n: int) -> bytes:
			return secrets.token_bytes(n)

	csrng: random.Random
	prng: Optional[random.Random]

	ciphertext: bytearray
	ciphertext_i: int

	eof: bool

	def __init__(self, key: bytes, wrapped: Optional[BinaryIO],
			this_uuid: Optional[uuid.UUID] = None,
			parent_uuid: Optional[uuid.UUID] = None,
			nonce_rng: Optional[random.Random] = None):
		super().__init__(key, wrapped, this_uuid, parent_uuid)

		self.csrng = nonce_rng if nonce_rng is not None \
				else self.CSRNG()
		self.prng = None

		self.ciphertext = bytearray()
		self.ciphertext_i = 0

		self.eof = False

	def newbuf(self) -> bytearray:
		# @rnd is the header's sequence number, which prevents
		# the reordering of ciphertexts.
		if not self.prng:
			rnd = self.csrng.getrandbits(self.RND_BITS)
			self.prng = self.mkprng(rnd)
		else:
			rnd = self.prng.getrandbits(self.RND_BITS)

		if self.this_uuid is not None:
			# Bind the ciphertext block to the UUIDs, preventing it
			# from being reused in another blob.
			cleartext = bytearray(self.header_st.size)
			self.header_st.pack_into(cleartext, 0,
				self.this_uuid_bytes, self.parent_uuid_bytes,
				rnd)
		else:
			cleartext = bytearray(self.partial_header_st.size)
			self.partial_header_st.pack_into(cleartext, 0, rnd)

		return cleartext

	def read(self, n: Optional[int] = None) -> Union[memoryview, bytearray]:
		assert self.wrapped is not None

		assert len(self.ciphertext) >= self.ciphertext_i
		ciphertext_len = len(self.ciphertext) - self.ciphertext_i
		if n is not None and n <= ciphertext_len:
			ciphertext = memoryview(self.ciphertext)[
					self.ciphertext_i:self.ciphertext_i+n]
			self.ciphertext_i += n
			if n == ciphertext_len:
				self.ciphertext = bytearray()
				self.ciphertext_i = 0
			return ciphertext

		if self.ciphertext_i > 0:
			try:
				del self.ciphertext[:self.ciphertext_i]
			except BufferError:
				# There could be an "Existing exports of data:
				# object cannot be re-sized" error if a view
				# of self.ciphertext returned earlier is still
				# held somewhere in the program.
				self.ciphertext = self.ciphertext[self.ciphertext_i:]
			self.ciphertext_i = 0

		while n is None or len(self.ciphertext) < n:
			cleartext = self.newbuf()
			minbuf = len(cleartext)

			while len(cleartext) < self.CLEARTEXT_SIZE \
					and not self.eof:
				prev = len(cleartext)
				cleartext += self.wrapped.read(
						self.CLEARTEXT_SIZE - prev)
				if len(cleartext) == prev:
					self.eof = True

			assert len(cleartext) <= self.CLEARTEXT_SIZE
			if len(cleartext) == minbuf:
				# Couldn't get more data from @self.wrapped.
				assert self.eof
				break
			assert len(cleartext) == self.CLEARTEXT_SIZE \
					or self.eof

			nonce = self.csrng.randbytes(self.NONCE_SIZE)
			self.ciphertext += nonce
			self.ciphertext += self.cipher.encrypt(
						nonce, bytes(cleartext), None)

		if n is None or len(self.ciphertext) <= n:
			ciphertext = self.ciphertext
			self.ciphertext = bytearray()
			return ciphertext
		else:
			ciphertext = memoryview(self.ciphertext)[:n]
			self.ciphertext_i = n
			return ciphertext

class Decrypt(Cipher):
	nonce: Optional[bytearray]
	prng: Optional[random.Random]
	ciphertext: bytearray

	inbytes: int
	outbytes: int

	def __init__(self, key: bytes, wrapped: Optional[BinaryIO],
			this_uuid: Optional[uuid.UUID] = None,
			parent_uuid: Optional[uuid.UUID] = None):
		super().__init__(key, wrapped, this_uuid, parent_uuid)

		self.nonce = None
		self.prng = None
		self.ciphertext = bytearray()

		self.inbytes = self.outbytes = 0

	def extract_nonce(self, buf: ByteString, buf_i: int = 0) \
			-> Optional[int]:
		if self.nonce is not None:
			return buf_i

		assert len(self.ciphertext) < self.NONCE_SIZE
		if len(self.ciphertext) + (len(buf) - buf_i) < self.NONCE_SIZE:
			self.ciphertext += buf[buf_i:]
			return None

		n = self.NONCE_SIZE - len(self.ciphertext)
		self.ciphertext += buf[buf_i:buf_i+n]
		self.nonce = self.ciphertext
		self.ciphertext = bytearray()
		self.inbytes += self.NONCE_SIZE
		return buf_i + n

	def verify_header(self, cleartext: memoryview) -> memoryview:
		if self.this_uuid is not None:
			header_st = self.header_st
			this_uuid, parent_uuid, rnd = \
				header_st.unpack_from(cleartext)
		else:
			header_st = self.partial_header_st
			this_uuid = parent_uuid = None
			rnd = header_st.unpack_from(cleartext)[0]

		if this_uuid is not None and this_uuid != self.this_uuid_bytes:
			this_uuid = uuid.UUID(bytes=this_uuid)
			raise SecurityError(
				"Subvolume UUID (%s) "
				"of block at offset in=%d/out=%d "
				"differs from expected (%s)"
				% (this_uuid,
					self.inbytes,
					self.outbytes,
					self.this_uuid))
		if parent_uuid is not None \
				and parent_uuid != self.parent_uuid_bytes:
			parent_uuid = uuid.UUID(bytes=parent_uuid)
			raise SecurityError(
				"Parent subvolume UUID (%s) "
				"of block at offset in=%d/out=%d "
				"differs from expected (%s)"
				% (parent_uuid,
					self.inbytes,
					self.outbytes,
					self.parent_uuid))

		if self.prng:
			expected_rnd = self.prng.getrandbits(self.RND_BITS)
			if rnd != expected_rnd:
				raise SecurityError(
					"Sequence number (0x%.16X) "
					"of block at offset in=%d/out=%d "
					"differs from expected (0x%.16X)"
					% (rnd, self.inbytes, self.outbytes,
						expected_rnd))
		else:
			self.prng = self.mkprng(rnd)

		assert len(cleartext) > header_st.size
		return cleartext[header_st.size:]

	def decrypt(self, ciphertext: ByteString) -> None:
		from cryptography import exceptions as cryptography_exceptions

		assert self.nonce is not None
		assert len(ciphertext) <= self.CIPHERTEXT_SIZE
		try:
			cleartext = memoryview(self.cipher.decrypt(
				self.nonce, bytes(ciphertext), None))
		except cryptography_exceptions.InvalidTag:
			raise SecurityError(
					"Decryption of ciphertext block "
					"at offset %d failed"
					% self.inbytes)

		cleartext = self.verify_header(cleartext)
		if self.wrapped is not None:
			self.wrapped.write(cleartext)
		self.inbytes += len(ciphertext)
		self.outbytes += len(cleartext)

		self.nonce = None
		if ciphertext is self.ciphertext:
			self.ciphertext = bytearray()

	def write(self, buf: ByteString) -> None:
		buf_i = self.extract_nonce(buf)
		if buf_i is None:
			return

		if self.ciphertext:
			n = min(len(buf) - buf_i,
				self.CIPHERTEXT_SIZE - len(self.ciphertext))
			self.ciphertext += buf[buf_i:buf_i+n]
			buf_i += n

			if len(self.ciphertext) < self.CIPHERTEXT_SIZE:
				return
			self.decrypt(self.ciphertext)

		while True:
			buf_i = self.extract_nonce(buf, buf_i)
			if buf_i is None:
				break

			assert not self.ciphertext
			if len(buf) - buf_i < self.CIPHERTEXT_SIZE:
				self.ciphertext = bytearray(buf[buf_i:])
				break

			self.decrypt(buf[buf_i:buf_i+self.CIPHERTEXT_SIZE])
			buf_i += self.CIPHERTEXT_SIZE

	def close(self) -> None:
		if self.ciphertext:
			if self.nonce is None:
				raise SecurityError(
					"%d trailing bytes at the end of the "
					"ciphertext" % len(self.ciphertext))
			self.decrypt(self.ciphertext)
		elif self.nonce is not None:
			raise SecurityError(
					"Empty block at the end of the "
					"ciphertext")
# }}}

# A class that reads from or writes to a wrapped file-like object, printing
# the progress periodically, keeping track of the @bytes_transferred, and if
# the @expected_bytes is known beforehand, ensuring that neither more nor less
# data is transferred.
class Progressometer: # {{{
	wrapped: Optional[BinaryIO]
	interval: Optional[float]

	expected_bytes: Optional[int]
	final_cb: Optional[Callable[None, None]]

	started: Optional[float] = None
	last_checkpoint_time: Optional[float] = None

	bytes_transferred: int = 0
	last_checkpoint_bytes: Optional[int] = None

	def __init__(self, f: Optional[BinaryIO],
			interval: Optional[float],
			expected_bytes: Optional[int] = None,
			final_cb: Optional[Callable[None, None]] = None):
		self.wrapped = f
		self.interval = interval
		self.expected_bytes = expected_bytes
		self.final_cb = final_cb

	def final_progress(self) -> None:
		if self.expected_bytes is not None:
			assert self.bytes_transferred <= self.expected_bytes
			if self.bytes_transferred < self.expected_bytes:
				missing = self.expected_bytes \
						- self.bytes_transferred
				raise SecurityError(
					f"Blob is missing {missing} bytes")

		print(f" %s (%s)" % (
				humanize_size(self.bytes_transferred),
				humanize_duration(
					time.monotonic() - self.started)),
			end="", flush=True)

	def make_progress(self) -> None:
		progress = humanize_size(self.bytes_transferred)
		if self.expected_bytes is not None:
			assert self.bytes_transferred <= self.expected_bytes
			done = self.bytes_transferred / self.expected_bytes
			progress = "%d%% (%s)" % (int(done * 100), progress)
		print(f" %s..." % progress, end="", flush=True)

	def check_progress(self) -> None:
		if self.interval is None:
			return

		now = time.monotonic()
		if self.last_checkpoint_time is None:
			self.started = now
			self.last_checkpoint_time = now
		elif now - self.last_checkpoint_time >= self.interval \
				and self.last_checkpoint_bytes \
					!= self.bytes_transferred:
			self.make_progress()
			self.last_checkpoint_time = now
			self.last_checkpoint_bytes = self.bytes_transferred

	def tell(self) -> int:
		return self.bytes_transferred

	def read(self, n: Optional[int] = None) -> bytes:
		assert self.wrapped is not None
		self.check_progress()

		buf = self.wrapped.read(n)
		if len(buf) < n:
			# blob.upload_from_file() won't call us anymore,
			# so it's our only chance to call final_cb().
			self.final_cb()

		self.bytes_transferred += len(buf)
		return buf

	def write(self, buf: bytes) -> None:
		self.check_progress()

		if self.expected_bytes is not None:
			if self.bytes_transferred + len(buf) \
					> self.expected_bytes:
				# Server is sending more data
				# than the blob's nominal size.
				raise SecurityError(
					"Blob is larger than expected")

		if self.wrapped is not None:
			self.wrapped.write(buf)
		self.bytes_transferred += len(buf)
# }}}

# A file-like object which can open a directory, closing the file descriptor
# automatically.
class OpenDir: # {{{
	fd: int

	def __init__(self, path: str):
		self.fd = os.open(path, os.O_RDONLY)

	def __del__(self):
		os.close(self.fd)

	def fileno(self) -> int:
		return self.fd
# }}}

# A chain of subprocesses.  When the Pipeline is deleted, its subprocesses
# are killed.
class Pipeline: # {{{
	def __init__(self,
			cmds: Sequence[Union[Sequence[str], Dict[str, Any]]],
			stdin=subprocess.DEVNULL, stdout=None):
		self.processes = [ ]
		for i, cmd in enumerate(cmds):
			if not self.processes:
				proc_stdin = stdin
			else:
				proc_stdin = self.processes[-1].stdout

			if i < len(cmds) - 1:
				proc_stdout = subprocess.PIPE
			else:
				proc_stdout = stdout

			if not isinstance(cmd, dict):
				cmd = { "args": cmd }
			self.processes.append(subprocess.Popen(**cmd,
				stdin=proc_stdin, stdout=proc_stdout))

	def __del__(self):
		for proc in self.processes:
			try: proc.kill()
			except: pass

	def __len__(self) -> int:
		return len(self.processes)

	def __getitem__(self, i: int) -> subprocess.Popen:
		return self.processes[i]

	def stdin(self) -> Optional[BinaryIO]:
		return self.processes[0].stdin if self.processes else None

	def stdout(self) -> Optional[BinaryIO]:
		return self.processes[-1].stdout if self.processes else None

	def wait(self) -> None:
		errors = [ ]
		for proc in self.processes:
			try:
				wait_proc(proc)
			except FatalError as ex:
				errors.append(ex.args[0])
		if errors:
			raise FatalError("\n".join(errors))
# }}}

# Utilities {{{
# Return the function's argument as a uuid.UUID.
def ensure_uuid(u: Union[None, uuid.UUID, bytes]) -> uuid.UUID:
	if u is None:
		return UUID0
	elif isinstance(u, uuid.UUID):
		return u
	else:
		return uuid.UUID(bytes=u)

# Wait for a subprocess and raise a FatalError if it exited with non-0 status.
def wait_proc(proc: subprocess.Popen) -> None:
	try:	# @proc might have execve()d another program (as is the case
		# with the @HEADER_VERIFICATION_SCRIPT), try to determine the
		# real identity of the executing program from its COMM.
		comm = open("/proc/%d/comm" % proc.pid)
	except FileNotFoundError:
		# Could be already reaped if we're called repeatedly.
		prog = proc.args[0]
	else:	# Wait until the subprocess finishes but don't reap it yet;
		# read its final COMM beforehand.
		os.waitid(os.P_PID, proc.pid, os.WEXITED | os.WNOWAIT)
		prog = comm.readline().rstrip()

	proc.wait()
	if proc.returncode > 0:
		raise FatalError(
			"%s exited with status %d"
			% (prog, proc.returncode))
	elif proc.returncode < 0:
		raise FatalError(
			"%s terminated with signal %d"
			% (prog, -proc.returncode))

# Convert a size in bytes into a fractional number of KiB/MiB/etc.
def humanize_size(size: int) -> str:
	if size < 1024:
		return "%d B" % size

	for unit in ("KiB", "MiB", "GiB", "TiB", "PiB"):
		size /= 1024.0
		if size < 1024:
			break
	return "%.2f %s" % (size, unit)

# Convert the @duration in seconds into "1h2m3s" format.
def humanize_duration(duration: float) -> str:
	duration = datetime.timedelta(seconds=duration)
	if duration.microseconds > 0:
		# Round it up to the next second.
		duration = datetime.timedelta(
				seconds=duration.seconds + 1)

	one_hour = datetime.timedelta(hours=1)
	one_minute = datetime.timedelta(minutes=1)

	hours = duration // one_hour
	duration %= one_hour
	minutes = duration // one_minute
	duration %= one_minute
	seconds = duration.seconds

	hms = ""
	if hours:
		hms += f"{hours}h"
	if minutes or (hours and seconds):
		hms += f"{minutes}m"
	if seconds or (not hours and not minutes):
		hms += f"{seconds}s"

	return hms

def woulda(args: argparse.Namespace, verb: str) -> str:
	if args.dry_run or getattr(args, "wet_run", False):
		return f"Would have {verb}"
	else:
		return verb.capitalize()
# }}}

# Subvolume-related functions {{{
# Return a subvolume's received UUID (if it was created by btrfs receive)
# or its own UUID.
def subvol_uuid(path: str) -> uuid.UUID:
	subvol = OpenDir(path)
	btrfs_ioctl_get_subvol_info_args = \
		bytearray(btrfs_ioctl_get_subvol_info_args_st.size)
	fcntl.ioctl(subvol, BTRFS_IOC_GET_SUBVOL_INFO,
			btrfs_ioctl_get_subvol_info_args)
	ret = btrfs_ioctl_get_subvol_info_args_st.unpack_from(
			btrfs_ioctl_get_subvol_info_args)

	# Return @recv_uuid unless it's all zeroes.
	self_uuid, recv_uuid = ret[6], ret[8]
	return uuid.UUID(bytes=recv_uuid if any(recv_uuid) else self_uuid)

# Delete a subvolume.  @fs must point to the parent subvolume.
def delete_subvol(fs: OpenDir, path: str) -> None:
	buf = bytearray(btrfs_ioctl_vol_args_v2_st.size)
	btrfs_ioctl_vol_args_v2_st.pack_into(buf, 0, path.encode())
	fcntl.ioctl(fs, BTRFS_IOC_SNAP_DESTROY_V2, buf)

# Delete a subvolume if not in dry-run mode.
def delete_snapshot(args: argparse.Namespace,
			fs: OpenDir, snapshot: Snapshot) -> None:
	if args.dry_run or getattr(args, "wet_run", False):
		print(f"Would delete {snapshot}.")
	else:
		print(f"Deleting {snapshot}...")
		delete_subvol(fs, snapshot.fname)
# }}}

# Snapshot-related functions {{{
# Go through the direct subdirectories of @path and return Snapshot:s
# for found subvolumes.
def discover_local_snapshots(path: str) -> Generator[Snapshot, None, None]:
	for dent in os.scandir(path):
		# Parse @dent.name before trying to retrieve its UUID.
		if not Snapshot.parse(dent.name):
			continue
		elif not dent.is_dir(follow_symlinks=False):
			continue

		# Is @dent the top-level directory of a subvolume?
		# stat(2) the full @dent.path because @dent.inode()
		# returns the inode of @path's subdirectory, not the
		# file system residing there.
		# This check was borrowed from btrfs-progs.
		if os.stat(dent.path).st_ino \
				!= btrfs.ctree.FIRST_FREE_OBJECTID:
			continue

		try:
			yield Snapshot(dent.name, subvol_uuid(dent.path))
		except OSError:
			# Not on a btrfs file system to begin with.
			pass

# Returns a dict of UUIDs -> Snapshots.
def uuid_to_snapshots(snapshots: Iterable[Snapshot]) \
			-> Dict[uuid.UUID, Snapshot]:
	return { snapshot.uuid: snapshot for snapshot in snapshots }
# }}}

# Backup-related functions {{{
# Go through the blobs of a GCS bucket and create Backup:s from them.
def discover_remote_backups(bucket: google.cloud.storage.Bucket,
				prefix: Optional[str] = None) \
				-> Dict[uuid.UUID, Backup]:
	if prefix is not None:
		prefix += '/'

	by_uuid = { }
	by_fname = { }
	for blob in bucket.list_blobs(prefix=prefix):
		fname, per, suffix = blob.name.rpartition('/')
		if not per:
			raise ConsistencyError(
					f"Invalid blob name {blob.name}")
		if suffix == "" and blob.size == 0:
			# Placeholder file for a directory.
			continue
		if suffix not in ("full", "delta"):
			raise ConsistencyError(
					f"{blob.name} has unknown suffix")
		if prefix is not None:
			assert fname.startswith(prefix)
			fname = fname.removeprefix(prefix)
		elif '/' in fname:
			# Ignore blobs that could have a prefix.
			continue

		if "uuid" not in blob.metadata:
			raise ConsistencyError(f"{blob.name} has no UUID")
		blob_uuid = uuid.UUID(blob.metadata["uuid"])

		if suffix == "delta" and "prev" not in blob.metadata:
			raise ConsistencyError(f"{blob.name} has no prev UUID")

		try:
			existing = by_fname[fname]
		except KeyError:
			existing = by_uuid.get(blob_uuid)
			if existing is not None:
				other = existing.full or existing.delta
				raise ConsistencyError(
					"%s and %s have the same UUID"
					% (blob.name, other.name))

			if suffix == "full":
				backup = Backup(fname, blob_uuid, full=blob)
			else:
				backup = Backup(fname, blob_uuid, delta=blob)
			by_uuid[blob_uuid] = by_fname[fname] = backup
		else:	# There's an @existing Backup.
			if suffix == "full":
				existing.set_full(blob)
				other = existing.delta
			else:
				existing.set_delta(blob)
				other = existing.full
			assert other is not None
			if blob_uuid != existing.uuid:
				raise ConsistencyError(
					"%s and %s have different UUIDs"
					% (blob.name, other.name))
	return by_uuid

# Is the Backup identified by its UUID a full backup or is it restorable
# from its parent Backup:s?
def backup_restorable(backup_uuid: Optional[uuid.UUID],
			remote_backups: Dict[uuid.UUID, Backup]) -> bool:
	if backup_uuid is None:
		return False
	backup = remote_backups.get(backup_uuid)
	if backup is None:
		return False

	if backup.restorable is None:
		if backup.full is not None:
			backup.restorable = True
		else:	# @backup only has a delta, determine if @backup.prev
			# is restorable, then cache the result.
			backup.restorable = backup_restorable(
						backup.prev, remote_backups)
	return backup.restorable
# }}}

# GCS-related functions {{{
# Create a google.cloud.storage.Client accessing GCS through the user-specified
# service account info.
def get_gcs_client(args: argparse.Namespace) -> google.cloud.storage.Client:
	cmd = None
	service_account_info = service_account_info_file = None
	if args.service_account_info_command is not None:
		assert isinstance(args.service_account_info_command, list)
		cmd = subprocess.Popen(args.service_account_info_command,
					stdout=subprocess.PIPE)
		service_account_info_file = cmd.stdout
	elif args.service_account_info_file is not None:
		assert isinstance(args.service_account_info_file, str)
		if args.service_account_info_file == '-':
			service_account_info_file = sys.stdin
		else:
			service_account_info_file = \
				open(args.service_account_info_file)
	elif args.service_account_info is not None:
		assert isinstance(args.service_account_info, dict)
		service_account_info = args.service_account_info

	if service_account_info_file is not None:
		import json
		service_account_info = json.load(service_account_info_file)
		if cmd is not None:
			wait_proc(cmd)

	if service_account_info is not None:
		creds = google.oauth2.service_account.Credentials. \
				from_service_account_info(service_account_info)
	else:
		creds = None

	return google.cloud.storage.Client(credentials=creds)

# Create a dict of { key: val|None } from a sequence of "key[=val]".
def parse_labels(labels: Iterable[str]) -> Dict[str, Optional[str]]:
	kw = { }
	for label in labels:
		key, eq, val = label.partition('=')
		kw[key] = val if eq else None
	return kw

# Returns whether a set of user-specified labels is a subset of a bucket's
# labels.
def labels_match(superset: Dict[str, str], subset: Dict[str, Optional[str]]) \
		-> bool:
	for key, val in subset.items():
		if key not in superset:
			return False
		if val is not None and superset[key] != val:
			return False
	return True

# Return the GCS bucket identified by its name or labels.
def find_bucket(gcs: google.cloud.storage.Client,
		bucket_name: Optional[str] = None,
		bucket_labels: Optional[List[str]] = None) \
		-> google.cloud.storage.Bucket:
	if bucket_name is not None:
		return gcs.bucket(bucket_name)

	assert bucket_labels is not None
	labels = parse_labels(bucket_labels)

	found = [ ]
	for bucket in gcs.list_buckets():
		if labels_match(bucket.labels, labels):
			found.append(bucket)

	if not found:
		raise UserError("Bucket not found")
	elif len(found) > 1:
		raise UserError("More than one buckets found")
	else:
		return found[0]

def get_retry_flags(args: argparse.Namespace) -> Dict[str, Any]:
	kwargs = { }
	if args.timeout is not None:
		kwargs["timeout"] = args.timeout
		kwargs["retry"] = google.cloud.storage.blob.DEFAULT_RETRY \
					.with_timeout(args.timeout)
	return kwargs
# }}}

# Snapshot selection {{{
# Return the index of a Snapshot in a sequence of Snapshot:s.
def find_snapshot(snapshots: Sequence[Snapshot],
			snapshots_by_uuid: Dict[uuid.UUID, Snapshot],
			what: Union[str, uuid.UUID],
			where: str) -> int:
	if isinstance(what, uuid.UUID):
		# Get @fname from UUID.
		try:
			fname = snapshots_by_uuid[what].fname
		except KeyError:
			raise UserError(f"{what} not found {where}")
	else:
		fname = what

	# @snapshots are ordered by key(), so we can bisect it.
	key: Callable[[Snapshot], str] = lambda snapshot: snapshot.fname

	class Snapshots:
		def __len__(self):
			return len(snapshots)
		def __getitem__(self, i: int):
			return key(snapshots[i])

	# TODO: replace with bisect.bisect_left(snapshots, fname, key=key)
	i = bisect.bisect_left(Snapshots(), fname)
	if i < len(snapshots) and key(snapshots[i]) == fname:
		return i
	raise UserError(f"{what} not found {where}")

# Return the indexes of multiple --exact snapshots.
def choose_exact_snapshots(args: argparse.Namespace, where: str,
				snapshots: Sequence[Snapshot],
				indexes: List[int]) -> bool:
	if not args.exact:
		return False
	assert not args.first and args.frm is None and args.to is None

	# Return the @indexes of @exacts in @snapshots.
	exacts = set(args.exact)
	for i, snapshot in enumerate(snapshots):
		try:
			if args.uuid:
				exacts.remove(snapshot.uuid)
			else:
				exacts.remove(snapshot.fname)
		except KeyError:
			pass
		else:
			indexes.append(i)
			if not exacts:
				break

	if exacts:
		# There are some @exacts we didn't find in @snapshots.
		errors = [ "The following snapshots were not found %s:"
				% where ]
		errors += ("  %s" % exact for exact in exacts)
		raise UserError("\n".join(errors))

	return True

# Return the index of the first and last snapshots selected by
# --first/--from/--to.
def choose_snapshot_range(args: argparse.Namespace, where: str,
				snapshots: Sequence[Snapshot],
				snapshots_by_uuid: Dict[uuid.UUID, Snapshot]) \
				-> Tuple[Optional[int], Optional[int]]:
	assert not args.exact

	# Determine the @last and @first snapshots in the range.
	if args.first:
		first = 0
	elif args.frm is not None:
		first = find_snapshot(snapshots, snapshots_by_uuid,
					args.frm, where)
	else:	# It depends on the caller.
		first = None

	if args.to is not None:
		last = find_snapshot(snapshots, snapshots_by_uuid,
					args.to, where)
	else:
		last = len(snapshots) - 1

	if not snapshots:
		assert args.frm is None and args.to is None
		return None, None

	if first is not None and last < first:
		# Only possible if --from and --to were specified wrongly.
		assert args.frm is not None and args.to is not None
		raise UserError(f"--to {args.to} precedes --from {args.frm}")

	return first, last

# Return the indexes of snapshots selected by --first/--from/--to/--exact.
def choose_snapshots(args: argparse.Namespace, where: str,
			snapshots: Sequence[Snapshot],
			snapshots_by_uuid: Dict[uuid.UUID, Snapshot]) \
			-> Collection[int]:
	exacts = [ ]
	if choose_exact_snapshots(args, where, snapshots, exacts):
		return exacts

	first, last = choose_snapshot_range(args, where,
						snapshots, snapshots_by_uuid)
	if first is not None:
		assert last is not None
		return range(first, last+1)
	else:
		assert last is None
		return ()
# }}}

# Metadata encryption {{{
CipherClass = TypeVar("CipherClass", bound=Cipher)
def get_cipher(args: argparse.Namespace, cipher_class: type[CipherClass],
		blob: google.cloud.storage.Blob,
		blob_uuid: uuid.UUID, parent_uuid: Optional[uuid.UUID]) \
		-> Union[None, Dict[str, Any], CipherClass]:
	if not args.encrypt:
		return None

	# Add environment variables that allow the external programs to retrieve
	# blob-specific keys.
	env = os.environ.copy()
	env["BUCKET_NAME"] = blob.bucket.name
	if args.prefix is not None:
		env["BLOB_PREFIX"] = args.prefix
	env["BLOB_UUID"] = str(blob_uuid)
	if parent_uuid is not None:
		env["PARENT_UUID"] = str(parent_uuid)

	if cipher_class is Encrypt and args.encryption_command is not None:
		return {
			"args": args.encryption_command,
			"env": env,
		}
	elif cipher_class is Decrypt and args.decryption_command is not None:
		return {
			"args": args.decryption_command,
			"env": env,
		}

	if args.encryption_key is not None:
		key = args.encryption_key
	else:
		assert args.encryption_key_command is not None
		key = subprocess.check_output(args.encryption_key_command, env=env)

	if not args.header:
		return cipher_class(key, wrapped=None)
	return cipher_class(key, wrapped=None,
				this_uuid=blob_uuid, parent_uuid=parent_uuid)

def encrypt_metadata(cipher: Union[Encrypt, Dict[str, Any]],
			this_uuid: Optional[uuid.UUID],
			parent_uuid: Optional[uuid.UUID],
			cleartext: bytes) -> str:
	if isinstance(cipher, Encrypt):
		ciphertext = Encrypt(cipher.key, io.BytesIO(cleartext),
				this_uuid, parent_uuid).read()
	else:
		if this_uuid is not None:
			# Bind this piece of metadata to the Backup.
			cleartext = this_uuid.bytes \
					+ ensure_uuid(parent_uuid).bytes \
					+ cleartext
		ciphertext = subprocess.check_output(**cipher, input=cleartext)

	return base64.b64encode(ciphertext).decode()

def decrypt_metadata(cipher: Union[Decrypt, Dict[str, Any]],
			this_uuid: Optional[uuid.UUID],
			parent_uuid: Optional[uuid.UUID],
			ciphertext: bytes) -> memoryview:
	ciphertext = base64.b64decode(ciphertext, validate=True)
	if isinstance(cipher, Decrypt):
		cleartext = io.BytesIO()
		cipher = Decrypt(cipher.key, cleartext, this_uuid, parent_uuid)
		cipher.write(ciphertext)
		cipher.close()
		return cleartext.getbuffer()

	cleartext = memoryview(subprocess.check_output(
				**cipher, input=ciphertext))
	if this_uuid is None:
		return cleartext

	header = this_uuid.bytes + ensure_uuid(parent_uuid).bytes
	if len(cleartext) < len(header):
		raise SecurityError("Invalid metadata")
	elif cleartext[:len(header)] != header:
		raise SecurityError("Metadata header mismatch")
	else:
		return cleartext[len(header):]
# }}}

# Upload backups to GCS {{{
# Write @blob_uuid and @parent_uuid as binary to @sys.stdout.
def write_header(blob_uuid: uuid.UUID, parent_uuid: Optional[uuid.UUID]) \
		-> Callable[[], None]:
	parent_uuid = ensure_uuid(parent_uuid)

	def write_header():
		# Redirect this function's stdout to stderr, so it doesn't
		# go into the pipeline by accident.
		btrfs_send_out, sys.stdout = sys.stdout, sys.stderr

		try:
			os.write(btrfs_send_out.fileno(), blob_uuid.bytes)
			os.write(btrfs_send_out.fileno(), parent_uuid.bytes)
		except Exception as ex:
			# The contents of exceptions are not passed back
			# to the main interpreter, so let's print it here.
			print(ex, file=sys.stderr)
			raise

	return write_header

def do_upload(args: argparse.Namespace,
		blob: google.cloud.storage.Blob,
		blob_uuid: uuid.UUID, parent_uuid: Optional[uuid.UUID],
		btrfs_send: Sequence[str]) -> int:
	if args.wet_run > 1:
		btrfs_send = (*btrfs_send, "--no-data")
	cipher = get_cipher(args, Encrypt, blob, blob_uuid, parent_uuid)
	if args.header and not isinstance(cipher, Encrypt):
		# Write @blob_uuid and @parent_uuid into the pipeline
		# before @btrfs_send is executed.  We rely on the pipe
		# having capacity for 32 bytes, otherwise there will be
		# a deadlock.
		#
		# If we're using Encrypt, it will add the headers itself.
		btrfs_send = {
			"args": btrfs_send,
			"preexec_fn": write_header(blob_uuid, parent_uuid),
		}

	pipeline = [ btrfs_send ]
	if args.compress is not None:
		pipeline.append(args.compress)
	if isinstance(cipher, dict):
		pipeline.append(cipher)
	pipeline = Pipeline(pipeline, stdout=subprocess.PIPE)

	if isinstance(cipher, Encrypt):
		cipher.init(pipeline.stdout())
		src = cipher
	else:
		src = pipeline.stdout()

	# Check the @pipeline for errors before returning the last read
	# to blob.upload_from_file().  If pipeline.wait() throws an exception
	# the upload will fail and not create the blob.
	src = Progressometer(src, args.progress, final_cb=pipeline.wait)

	if not args.wet_run:
		try:
			flags = get_retry_flags(args)
			if args.reupload:
				# The blob to update must exist.
				flags["if_generation_not_match"] = 0
			else:	# The blob must not exist yet.
				flags["if_generation_match"] = 0
			if args.upload_chunk_size is not None:
				blob.chunk_size = args.upload_chunk_size \
							* 1024 * 1024
			blob.upload_from_file(src, checksum="md5", **flags)
		except google.api_core.exceptions.PreconditionFailed as ex:
			raise ConsistencyError("%s already exists in bucket"
						% blob.name)
		except google.api_core.exceptions.GoogleAPICallError as ex:
			raise FatalError from ex
	else:	# In case of --wet-run just read @src until we hit EOF.
		if not args.force_wet_run \
				and blob.bucket.get_blob(blob.name) != None:
			raise ConsistencyError("%s already exists in bucket"
						% blob.name)
		while src.read(1024*1024):
			pass

	src.final_progress()

	if not args.wet_run and blob.size != src.bytes_transferred:
		# GCS has a different idea about the blob's size than us.
		try:
			blob.delete()
		except:	# We may not have permission to do so.
			print(f"WARNING: {blob.name} could be corrupted, "
				"but unable to delete it!", file=sys.stderr)
		raise ConsistencyError("Blob size mismatch (%d, expected %d)"
					% (blob.size, src.bytes_transferred))

	if cipher is not None and args.verify_blob_size:
		size = encrypt_metadata(cipher, blob_uuid, parent_uuid,
				src.bytes_transferred.to_bytes(8, "big"))
		blob.metadata = { "expected_size":  size }
		if not args.wet_run:
			# If this fails the blob won't be usable without
			# --no-verify-blob-size, so it's okay to keep it.
			blob.patch()

	return src.bytes_transferred

def make_blob(bucket: google.cloud.storage.Bucket,
		prefix: Optional[str], snapshot: Snapshot, suffix: str,
		metadata: Dict[str, str] = { }) \
		-> google.cloud.storage.Blob:
	blob_name = f"{snapshot.fname}/{suffix}"
	if prefix is not None:
		blob_name = f"{prefix}/{blob_name}"
	blob = bucket.blob(blob_name)

	metadata["uuid"] = str(snapshot.uuid)
	blob.metadata = metadata

	return blob

def upload_full(args: argparse.Namespace,
		bucket: google.cloud.storage.Bucket,
		snapshot: Snapshot) -> int:
	if args.dry_run:
		print(f"Would upload {snapshot} in full.")
		return 0

	print(f"Uploading {snapshot} in full...", end="", flush=True)
	try:
		return do_upload(args,
			make_blob(bucket, args.prefix, snapshot, "full"),
			snapshot.uuid, None,
			("btrfs", "-q", "send",
				os.path.join(args.dir, snapshot.fname)))
	finally:
		print()

def upload_delta(args: argparse.Namespace,
		bucket: google.cloud.storage.Bucket,
		snapshot: Snapshot, parent: Snapshot) -> int:
	if args.dry_run:
		print(f"Would upload {snapshot} delta from {parent}.")
		return 0

	print(f"Uploading {snapshot} delta from {parent}...",
		end="", flush=True)
	try:
		return do_upload(args,
			make_blob(bucket, args.prefix, snapshot, "delta",
					{"prev": str(parent.uuid)}),
			snapshot.uuid, parent.uuid,
			("btrfs", "-q", "send",
				"-p", os.path.join(args.dir, parent.fname),
				os.path.join(args.dir, snapshot.fname)))
	finally:
		print()

def cmd_upload(args: argparse.Namespace) -> None:
	local_by_uuid = uuid_to_snapshots(discover_local_snapshots(args.dir))
	local_snapshots = sorted(local_by_uuid.values())

	gcs = get_gcs_client(args)
	bucket = find_bucket(gcs, args.bucket, args.bucket_label)
	remote_backups = discover_remote_backups(bucket, args.prefix) \
				if not args.force_wet_run else { }

	# Figure out what @to_upload.
	to_upload = [ ]
	if args.reupload:
		# Only reupload what is already present remotely.
		remote_backup_list = sorted(remote_backups.values())
		if not choose_exact_snapshots(args, "remotely",
						remote_backup_list,
						to_upload):
			first, last = choose_snapshot_range(
						args, "remotely",
						remote_backup_list,
						remote_backups)
			if last is None:
				print("Nothing to upload.")
				return
			if first is None:
				first = 0
			to_upload = range(first, last+1)

		# Translate indexes from @remote_backup_list to
		# @local_snapshots and verify the ordering.
		fun = lambda i: find_snapshot(
					local_snapshots, local_by_uuid,
					remote_backup_list[i].uuid, "locally")
		to_upload = list(map(fun, to_upload))
		assert all(lhs < rhs for lhs, rhs
				in zip(to_upload, to_upload[1:]))
	elif not choose_exact_snapshots(args, "locally", local_snapshots,
					to_upload):
		first, last = choose_snapshot_range(args, "locally",
							local_snapshots,
							local_by_uuid)
		if last is None:
			print("Nothing to upload. (Wrong directory?)")
			return
		if first is None:
			# Choose the @first snapshot to upload.
			if args.prefer_full or args.force_full:
				# Just upload the @last in full.
				first = last
			else:	# Find the @first @snapshot in @remote_backups
				# from the @last one backwards.
				for first in range(last, -1, -1):
					snapshot = local_snapshots[first]
					if snapshot.uuid in remote_backups:
						break
				else:	# We didn't find any.
					# If --force-delta, leave @first == 0
					# and an error will be thrown later.
					# Otherwise @first will be uploaded
					# in full.
					assert first == 0
		to_upload = range(first, last+1)

	print("Considering to upload:")
	for i in to_upload:
		print("  %s" % local_snapshots[i])
	print()

	fs = OpenDir(args.dir) if args.autodelete else None
	prev_uploaded = None
	ndeleted = 0

	# Upload snapshots.
	bytes_transferred = 0
	snapshots_transferred = 0
	started = time.monotonic()
	for i in to_upload:
		snapshot = local_snapshots[i]
		backup = remote_backups.get(snapshot.uuid)
		if i > 0 and local_snapshots[i-1].uuid in remote_backups:
			parent = local_snapshots[i-1]
			if backup is not None and backup.prev is not None \
					and backup.prev != parent.uuid:
				# @parent is not the parent of @snapshot
				# (it's missing from @local_snapshots).
				parent = None
		else:	# We can't upload a delta.
			parent = None

		# @should_upload_full or @should_upload_delta?
		should_upload_full = should_upload_delta = False
		if args.reupload:
			# User could only select @backup:s
			# from @remote_backups.
			assert backup is not None

			# Don't "continue" even if skipping this @backup,
			# because we still need to check for autodeletion.
			if args.prefer_full or args.force_full:
				if backup.full is None:
					msg = "%s doesn't have a full backup" \
						% backup
					if args.force_full:
						raise UserError(msg)
					print(f"{msg}, skipping.")
				else:
					should_upload_full = True
			elif args.prefer_delta or args.force_delta:
				if backup.delta is None:
					msg = "%s doesn't have an " \
						"incremental backup" % backup
					if args.force_delta:
						raise UserError(msg)
					print(f"{msg}, skipping.")
					continue
				elif parent is None:
					msg = "Parent of %s not found locally" \
						% backup
					if args.force_delta:
						raise UserError(msg)
					print(f"{msg}, skipping.")
				else:
					should_upload_delta = True
			else:
				should_upload_full = backup.full is not None
				if backup.delta is not None:
					if parent is None:
						print("Parent of %s "
							"not found locally, "
							"skipping." % backup)
					else:
						should_upload_delta = True
		elif args.prefer_full or args.force_full:
			if backup is None:
				should_upload_full = True
			elif backup.full is None and args.force_full:
				should_upload_full = True
		elif backup is None:
			# --prefer-delta by default
			if parent is not None:
				should_upload_delta = True
			elif args.force_delta:
				raise UserError(
					"Would need to upload %s in full"
					% snapshot)
			else:
				should_upload_full = True
		elif backup.delta is None and args.force_delta:
			# The first snapshot is always full.
			assert backup.full is not None
			if parent is None and i > 0:
				raise UserError(
					"Parent of %s not found remotely"
					% snapshot)
			should_upload_delta = parent is not None

		# Upload @snapshot.
		if should_upload_full:
			bytes_transferred += upload_full(args, bucket, snapshot)
			snapshots_transferred += 1
		if should_upload_delta:
			assert parent is not None
			bytes_transferred += upload_delta(args, bucket, snapshot, parent)
			snapshots_transferred += 1
		if should_upload_full or should_upload_delta:
			remote_backups[snapshot.uuid] = snapshot
		else:
			assert backup is not None
			if not args.reupload:
				print(f"{snapshot} is already backed up.")

		# --autodelete
		if prev_uploaded is not None:
			assert prev_uploaded is not local_snapshots[-1]
			delete_snapshot(args, fs, prev_uploaded)
			ndeleted += 1
		if args.autodelete:
			prev_uploaded = snapshot

	if snapshots_transferred > 1:
		msg = [
			woulda(args, "uploaded"),
			f"{snapshots_transferred} snapshots",
		]
		if not args.dry_run:
			duration = time.monotonic() - started
			msg.append("(%s)" % humanize_size(bytes_transferred))
			msg.append("in %s" % humanize_duration(duration))

		print()
		print("%s." % ' '.join(msg))
		if ndeleted > 0:
			print("Also %s %d snapshot(s)."
				% (woulda(args, "deleted").lower(), ndeleted))
# }}}

# Download backups from GCS and create subvolumes from them {{{
# Read a pair of UUIDs from stdin and compare them to the expected ones
# passed through sys.argv.  If they check out, execute sys.argv[4].
HEADER_VERIFICATION_SCRIPT = """
import sys, os
import uuid

# Set a more informative COMM than "python3" for wait_proc().
try:
	fd = os.open("/proc/self/comm", os.O_WRONLY)
except FileNotFoundError:
	pass
else:
	os.write(fd, b"verify_header")
	os.close(fd)

# Verify the blob's UUID.  sys.argv[0] is "-c".
expected = uuid.UUID(sys.argv[1])
actual = uuid.UUID(bytes=os.read(sys.stdin.fileno(), len(expected.bytes)))
if actual != expected:
	sys.exit("Blob's UUID (%s) differs from expected (%s)."
			% (actual, expected))

# Verify the blob's parent UUID.
expected = uuid.UUID(sys.argv[2])
actual = uuid.UUID(bytes=os.read(sys.stdin.fileno(), len(expected.bytes)))
if actual != expected:
	sys.exit("Blob's parent UUID (%s) differs from expected (%s)."
			% (actual, expected))

# Execute btrfs receive.
os.execvp(sys.argv[3], sys.argv[3:])
"""

def do_download(args: argparse.Namespace,
		fname: str,
		blob: google.cloud.storage.Blob,
		blob_uuid: uuid.UUID, parent_uuid: Optional[uuid.UUID],
		btrfs_recv: Sequence[str]) -> int:
	if not args.force_wet_run and os.path.exists(
					os.path.join(args.dir, fname)):
		raise UserError(f"{fname} already exists")

	cipher = get_cipher(args, Decrypt, blob, blob_uuid, parent_uuid)
	if cipher is not None and args.verify_blob_size:
		if "expected_size" not in blob.metadata:
			raise SecurityError(
				"%s is missing expected_size metadata"
				% blob.name)
		expected_size = int.from_bytes(
				decrypt_metadata(cipher, blob_uuid, parent_uuid,
					blob.metadata["expected_size"]),
				"big")
		if blob.size != expected_size:
			raise SecurityError("%s has unexpected size (%d != %d)"
					% (blob.name, blob.size, expected_size))

	if not args.wet_run:
		# We'll need to parse @btrfs_recv's output.
		btrfs_recv = { "args": btrfs_recv }
		if parent_uuid is None:
			# @btrfs_recv prints "At subvol ..." on stderr.
			btrfs_recv["stderr"] = subprocess.PIPE
			pipeline_stdout = None
		else:	# @btrfs_recv prints "At snapshot ..." on stdout.
			pipeline_stdout = subprocess.PIPE
	else:	# --wet-run
		pipeline_stdout = subprocess.DEVNULL
		if args.wet_run == 1:
			btrfs_recv = { "args": (*btrfs_recv[:-1], "--dump") }
		elif args.header and not isinstance(cipher, Decrypt):
			btrfs_recv = { "args": ("cat",) }
		else:
			btrfs_recv = None

	if args.header and not isinstance(cipher, Decrypt):
		# Wrap @btrfs_recv with the @HEADER_VERIFICATION_SCRIPT,
		# and pass it the expected UUIDs.
		assert isinstance(btrfs_recv, dict)
		btrfs_recv["args"] = \
			("python3", "-c", HEADER_VERIFICATION_SCRIPT,
				str(blob_uuid),
				str(ensure_uuid(parent_uuid))) \
			+ btrfs_recv["args"]
		btrfs_recv["executable"] = sys.executable

	pipeline = [ ]
	if isinstance(cipher, dict):
		pipeline.append(cipher)
	if args.compress is not None:
		pipeline.append(args.compress)
	if btrfs_recv is not None:
		pipeline.append(btrfs_recv)

	# @btrfs_recv writes the snapshot it creates to its stdout or stderr.
	# This can be different from the intended destination @fname in case
	# the backup was renamed in GCS.
	def extract_new_subvol() -> Optional[str]:
		if len(pipeline) > 0:
			# This should cause the @pipeline to finish.
			pipeline.stdin().close()

		if args.wet_run:
			return None
		assert len(pipeline) > 0

		# The message is different if we restore from delta or not.
		if parent_uuid is None:
			fin = pipeline[-1].stderr
			fout = sys.stderr
			subvol_pattern = re.compile("^At subvol (.+)\n")
		else:
			fin = pipeline[-1].stdout
			fout = sys.stdout
			subvol_pattern = re.compile("^At snapshot (.+)\n")

		# Parse @fin for @subvol_pattern.
		out = io.TextIOWrapper(fin).read()
		subvol = subvol_pattern.match(out)
		if subvol:
			# Remove @subvol_pattern from @out.
			out = subvol_pattern.sub("", out)

		if out:	# Print @out as if it was output by @btrfs_recv.
			# Make it more visible by adding a newline.
			print()
			fout.write(out)

		return subvol.group(1) if subvol else None

	# @pipeline could be empty.
	pipeline = Pipeline(pipeline,
				stdin=subprocess.PIPE,
				stdout=pipeline_stdout)
	if isinstance(cipher, Decrypt):
		cipher.init(pipeline.stdin())
		dst = cipher
	else:
		dst = pipeline.stdin()
	dst = Progressometer(dst, args.progress, blob.size)

	try:	# The actual download.
		blob.download_to_file(dst, **get_retry_flags(args))
		dst.final_progress()
		if isinstance(cipher, Decrypt):
			cipher.close()
	except (Exception, KeyboardInterrupt) as ex:
		subvol = extract_new_subvol()
		if subvol is not None:
			# Don't leave behind a potentially corrupted snapshot.
			delete_subvol(OpenDir(args.dir), subvol)

		if isinstance(ex, google.api_core.exceptions
					.GoogleAPICallError):
			raise FatalError from ex
		raise

	# Read the output of @pipeline before waiting for it, otherwise we could
	# end up in a deadlock, the @pipeline waiting to be read.
	subvol = extract_new_subvol()
	try:
		pipeline.wait()
	except:
		if subvol is not None:
			delete_subvol(OpenDir(args.dir), subvol)
		raise

	if subvol is not None and subvol != fname:
		os.rename(os.path.join(args.dir, subvol),
				os.path.join(args.dir, fname))

	# If there's a mismatch Progressometer.final_progress() should have
	# caught it.
	assert dst.bytes_transferred == blob.size
	return dst.bytes_transferred

def download_full(args: argparse.Namespace, backup: Backup) -> int:
	size = humanize_size(backup.full.size)
	if args.dry_run:
		print(f"Would download {backup} in full ({size}).")
		return backup.full.size

	print(f"Downloading {backup} in full ({size})...", end="", flush=True)
	try:
		return do_download(args,
			backup.fname, backup.full, backup.uuid, None,
			("btrfs", "receive", args.dir))
	finally:
		print()

def download_delta(args: argparse.Namespace, backup: Backup,
			parent: Snapshot) -> int:
	size = humanize_size(backup.delta.size)
	if args.dry_run:
		print(f"Would download {backup} delta from {parent} ({size}).")
		return backup.delta.size

	print(f"Downloading {backup} delta from {parent} ({size})...",
		end="", flush=True)
	try:
		return do_download(args,
			backup.fname, backup.delta, backup.uuid, parent.uuid,
			("btrfs", "receive", args.dir))
	finally:
		print()

def cmd_download(args: argparse.Namespace) -> None:
	local_snapshots = \
		uuid_to_snapshots(discover_local_snapshots(args.dir)) \
		if not args.force_wet_run else { }

	gcs = get_gcs_client(args)
	bucket = find_bucket(gcs, args.bucket, args.bucket_label)
	remote_by_uuid = discover_remote_backups(bucket, args.prefix)
	remote_backups = sorted(remote_by_uuid.values())

	# Validate the parent-child relationships in @remote_backups.
	for i, backup in enumerate(remote_backups):
		if backup.prev is None:
			continue
		parent = remote_by_uuid.get(backup.prev)
		if parent is None:
			continue
		if i == 0 or parent != remote_backups[i-1]:
			raise ConsistencyError("%s has invalid parent %s"
						% (backup, parent))

	# Figure out what @to_download.
	to_download = [ ]
	if choose_exact_snapshots(args, "remotely", remote_backups,
					to_download):
		to_download = [ remote_backups[i] for i in to_download ]
	else:
		first, last = choose_snapshot_range(args, "remotely",
							remote_backups,
							remote_by_uuid)
		if last is None:
			print("Nothing to download.")
			return
		if first is not None:
			to_download = [ remote_backups[i] for i
					in range(first, last+1) ]
		elif args.force_full:
			# If it doesn't have a full backup an error
			# will be thrown later.
			to_download = [ remote_backups[last] ]
		else:	# Choose the @first backup to download.
			first_full = None
			to_download = [ ]
			backup = remote_backups[last]
			while backup is not None:
				to_download.insert(0, backup)
				if backup.uuid in local_snapshots:
					break
				if backup.full is not None \
						and not args.force_delta:
					if args.prefer_full:
						# Start downloading
						# from this @backup.
						break
					elif first_full is None:
						first_full = len(to_download)
				backup = remote_by_uuid.get(backup.prev)

			if backup is None and first_full is not None:
				# Didn't find any @backup in @local_snapshots.
				# Start downloading with @first_full.
				del to_download[0:-first_full]

	print("Considering to download:")
	for backup in to_download:
		print("  %s" % backup)
	print()

	fs = OpenDir(args.dir) if args.autodelete else None
	prev_downloaded = None

	# Download backups.
	bytes_transferred = 0
	backups_transferred = 0
	started = time.monotonic()
	for backup in to_download:
		if backup.uuid in local_snapshots:
			print(f"Subvolume for {backup} already exists.")
			continue

		if backup.prev is not None:
			parent = local_snapshots.get(backup.prev)
		else:
			parent = None

		# @should_download_delta?
		if args.force_full:
			if backup.full is None:
				raise UserError(
					f"{backup} doesn't have a full backup")
			should_download_delta = False
		elif args.force_delta:
			if backup.delta is None:
				raise UserError(
					f"Would need to download {backup} "
					"in full")
			if parent is None:
				raise UserError(
					f"{backup.prev} (parent of {backup}) "
					"not found locally")
			should_download_delta = True
		elif parent is not None:
			# --prefer-delta by default
			should_download_delta = not args.prefer_full \
						or backup.full is None
		elif backup.full is not None:
			should_download_delta = False
		else:
			raise UserError(
				f"{backup.prev} (parent of {backup}) "
				"not found locally")

		if should_download_delta:
			assert parent is not None
			n = download_delta(args, backup, parent)
		else:
			assert prev_downloaded is None
			n = download_full(args, backup)
		local_snapshots[backup.uuid] = backup

		bytes_transferred += n
		backups_transferred += 1

		# --autodelete
		if prev_downloaded is not None:
			delete_snapshot(args, fs, prev_downloaded)
			del local_snapshots[prev_downloaded.uuid]
		if args.autodelete:
			prev_downloaded = backup

	if backups_transferred > 1:
		msg = [
			woulda(args, "downloaded"),
			f"{backups_transferred} backups",
			"(%s)" % humanize_size(bytes_transferred),
		]
		if not args.dry_run:
			duration = time.monotonic() - started
			msg.append("in %s" % humanize_duration(duration))

		print()
		print("%s." % ' '.join(msg))
# }}}

# List commands {{{
def cmd_list_buckets(args: argparse.Namespace) -> None:
	gcs = get_gcs_client(args)

	labels = parse_labels(args.bucket_label) \
		if args.bucket_label is not None \
		else None

	found = False
	for bucket in gcs.list_buckets():
		if args.bucket is not None and bucket.name != args.bucket:
			continue
		if labels is not None and not labels_match(bucket.labels,
								labels):
			continue
		labels = ", ".join(
			key if not val else "%s=%s" % (key, repr(val))
			for key, val in bucket.labels.items())
		if labels:
			print(bucket.name, labels)
		else:
			print(bucket.name)
		found = True

	if not found:
		raise UserError("Bucket not found")

def cmd_list_local(args: argparse.Namespace) -> None:
	if args.check_remote:
		assert args.bucket is not None or args.bucket_label is not None
		gcs = get_gcs_client(args)
		bucket = find_bucket(gcs, args.bucket, args.bucket_label)
		remote_backups = discover_remote_backups(bucket, args.prefix)
	else:
		remote_backups = None

	for snapshot in sorted(discover_local_snapshots(args.dir)):
		if remote_backups is None:
			print(snapshot)
		elif snapshot.uuid in remote_backups:
			print("%s: present remotely" % snapshot)
		else:
			print("%s: absent remotely" % snapshot)

def cmd_list_remote(args: argparse.Namespace) -> None:
	if args.dir is not None:
		local_snapshots = uuid_to_snapshots(
					discover_local_snapshots(args.dir))
	else:
		local_snapshots = None

	gcs = get_gcs_client(args)
	bucket = find_bucket(gcs, args.bucket, args.bucket_label)
	remote_backups = discover_remote_backups(bucket, args.prefix)

	nbytes = 0
	nbackups = 0
	for backup in sorted(remote_backups.values()):
		postfixes = [ ]
		if backup.full is not None:
			postfixes.append(
				"full: %s" % humanize_size(backup.full.size))
			nbackups += 1
			nbytes += backup.full.size
		if backup.delta is not None:
			postfixes.append(
				"delta: %s" % humanize_size(backup.delta.size))
			nbackups += 1
			nbytes += backup.delta.size
		line = "%s (%s)" % (backup, ", ".join(postfixes))

		if local_snapshots is None or backup.uuid in local_snapshots:
			print(line)
		else:
			print("%s: absent locally" % line)

	if nbackups > 1:
		print()
		print("%d backups in %s." % (nbackups, humanize_size(nbytes)))
# }}}

# Delete commands {{{
def snapshot_restorable(snapshot: Snapshot,
			remote_backups: Dict[uuid.UUID, Backup]) -> bool:
	return backup_restorable(snapshot.uuid, remote_backups)

def cmd_delete_local(args: argparse.Namespace) -> None:
	local_by_uuid = uuid_to_snapshots(discover_local_snapshots(args.dir))
	local_snapshots = sorted(local_by_uuid.values())

	# We don't need to consider the @remote_backups if --force-all.
	if not args.force_all:
		assert args.bucket is not None or args.bucket_label is not None
		gcs = get_gcs_client(args)
		bucket = find_bucket(gcs, args.bucket, args.bucket_label)
		remote_backups = discover_remote_backups(bucket, args.prefix)

	# Figure out what @to_delete.
	to_delete = choose_snapshots(args, "locally",
					local_snapshots, local_by_uuid)
	if not to_delete:
		print("Nothing to delete. (Wrong directory?)")
		return

	print("Considering to delete:")
	for i in to_delete:
		print("  %s" % local_snapshots[i])
	print()

	# Delete snapshots.
	ndeleted = 0
	fs = OpenDir(args.dir)
	for i in to_delete:
		snapshot = local_snapshots[i]
		if not args.force_all:
			assert remote_backups is not None
			if not snapshot_restorable(snapshot, remote_backups):
				print("%s is not restorable from backups, "
					"skipping." % snapshot)
				continue
			elif args.force:
				pass
			elif i+1 < len(local_snapshots):
				child = local_snapshots[i+1]
				if child.uuid not in remote_backups:
					print("%s is necessary to make "
						"an incremental backup "
						"of %s, skipping."
						% (snapshot, child))
					continue
			elif args.last:
				# Don't delete the newest snapshot unless
				# explicitly requested with --to or --exact.
				print("%s would be necessary to make "
					"an incremental backup "
					"of a new snapshot, skipping."
					% snapshot)
				continue

		delete_snapshot(args, fs, snapshot)
		ndeleted += 1

	if ndeleted > 0:
		print()
		print("%s %d snapshot(s)."
			% (woulda(args, "deleted"), ndeleted))
	else:
		print("Would not have deleted anything.")

def cmd_delete_remote(args: argparse.Namespace) -> None:
	# Only take @local_snapshots into account if --force:d.
	local_snapshots = \
		uuid_to_snapshots(discover_local_snapshots(args.dir)) \
		if args.force else { }

	gcs = get_gcs_client(args)
	bucket = find_bucket(gcs, args.bucket, args.bucket_label)
	remote_by_uuid = discover_remote_backups(bucket, args.prefix)
	remote_backups = sorted(remote_by_uuid.values())

	# Figure out what @to_delete.
	to_delete = choose_snapshots(args, "remotely",
					remote_backups, remote_by_uuid)
	if not to_delete:
		print("Nothing to delete.")
		return

	print("Considering to delete:")
	for i in to_delete:
		print("  %s" % remote_backups[i])
	print()

	# @which_to_delete: FULL and/or DELTA?
	# --delete-full:		[ FULL ]
	# --delete-delta:		[ DELTA ]
	# --delete-full-delta:		[ FULL, DELTA ]
	# --delete-delta-full:		[ DELTA, FULL ]
	# --delete-delta-broken:	[ ]
	FULL = object()
	DELTA = object()
	which_to_delete = [ ]
	if args.delete_full or args.delete_full_delta:
		which_to_delete.append(FULL)
	elif args.delete_delta or args.delete_delta_full:
		which_to_delete.append(DELTA)
	if args.delete_full_delta:
		which_to_delete.append(DELTA)
	elif args.delete_delta_full:
		which_to_delete.append(FULL)

	# Delete snapshots.
	ndeleted = 0
	deleted_bytes = 0
	for i in to_delete:
		backup = remote_backups[i]

		# In other words:
		#
		# Delete FULL?
		# 	if --delete-full or --delete-full-delta:
		# 		if force and present locally:
		# 			delete FULL (present)
		# 		elif restorable from DELTA:
		# 			delete FULL (restorable)
		# 	elif --delete-delta:
		# 		don't delete FULL
		# 	elif --delete-delta-full:
		# 		if force and present locally:
		# 			delete FULL (present)
		#
		# Delete DELTA?
		# 	if --delete-delta or --delete-delta-full:
		# 		if force and present locally:
		# 			delete DELTA (present)
		# 		elif FULL exists:
		# 			delete DELTA (full)
		# 		elif not restorable from DELTA:
		# 			delete DELTA (broken)
		# 	elif --delete-full:
		# 		don't delete DELTA
		# 	elif --delete-full-delta:
		# 		if force and present locally:
		# 			delete DELTA (present)
		# 		elif not restorable from DELTA:
		# 			delete DELTA (broken)
		what_to_delete = [ ]
		if args.force_all or backup.uuid in local_snapshots:
			# --force or --force-all
			reason = "snapshot is present locally" \
				if not args.force_all else None
			if FULL in which_to_delete:
				what_to_delete.append((backup, backup.full,
							reason))
			if DELTA in which_to_delete:
				what_to_delete.append((backup, backup.delta,
							reason))
		elif which_to_delete and which_to_delete[0] == DELTA \
				and backup.full is not None:
			what_to_delete.append((
					backup, backup.delta,
					"full backup is available"))
		elif backup_restorable(backup.prev, remote_by_uuid):
			if which_to_delete and which_to_delete[0] == FULL:
				what_to_delete.append((
					backup, backup.full,
					"backup is restorable incrementally"))
		else:	# Not restorable from DELTA.
			if DELTA in which_to_delete \
					or args.delete_delta_broken:
				what_to_delete.append((
					backup, backup.delta,
					"incremental backup chain is broken"))

		for backup, blob, reason in what_to_delete:
			if blob is None:
				continue
			ndeleted += 1
			deleted_bytes += blob.size

			details = [ ]
			if args.show_uuid:
				details.append(str(backup.uuid))
			details.append(humanize_size(blob.size))
			if reason is not None:
				details.append(reason)
			details = ", ".join(details)

			if args.dry_run:
				print("Would delete %s (%s)."
					% (blob.name, details))
				continue

			print("Deleting %s (%s)..." % (blob.name, details))
			blob.delete()

	if ndeleted > 0:
		print()
		print("%s %d backups(s) (%s)."
			% (woulda(args, "deleted"), ndeleted,
				humanize_size(deleted_bytes)))
	else:
		print("Would not have deleted anything.")
# }}}

# Search for a config file in:
# * --config
# * $BTRFS_BACKUP_ARCHIVE_CONFIG
# * args.dir or .
# * $HOME
# * /etc
def find_config_file(args: argparse.Namespace) -> Optional[str]:
	if args.config is not None:
		return args.config

	config = os.environ.get("BTRFS_BACKUP_ARCHIVE_CONFIG")
	if config is not None:
		return config

	dot_config = f".{CONFIG_FILE}"
	if args.dir is not None and args.dir != '.':
		config = os.path.join(args.dir, dot_config)
	else:
		config = dot_config
	if os.path.exists(config):
		return config

	home = os.environ.get("HOME")
	if home is None:
		import pwd

		try: home = pwd.getpwuid(os.getuid()).pw_dir
		except KeyError: pass
	if home is not None:
		config = os.path.join(home, dot_config)
		if os.path.exists(config):
			return config

	config = os.path.join("/etc", CONFIG_FILE)
	if os.path.exists(config):
		return config

	return None

def add_options_from_ini(args: argparse.Namespace,
		ini: ConfigParser, section: str,
		*options: Sequence[str], tpe: type = str) -> None:
	# Are any of the @options specified through the command line?
	for key in options:
		if getattr(args, key, None) is not None:
			# Don't even look at @ini.  It is assumed that
			# only one option is set in @args.
			return

	# Collect options set in the @default and @non_default sections
	# of @ini.
	default = { }
	non_default = { }
	for key in options:
		try:
			val = ini.get(section, key)
		except configparser.NoOptionError:
			continue

		# @lst to add @val.
		lst = default if ini.is_default(val) else non_default

		# Get the right @val based on @tpe.
		if tpe is bool:
			val = ini.getboolean(section, key)
		elif tpe is int:
			val = ini.getint(section, key)

		lst[key] = val

	# Verify that the @default or @non_default section doesn't have
	# conflicting (more than one) options.  However it's OK to have
	# one option in the @default section being overridden by another
	# in the @non_default.
	effective = non_default or default
	if len(effective) > 1:
		sys.exit("%s: conflicting options in section %s: %s"
				% (ini.filenames[0], section,
					", ".join(effective.keys())))
	elif len(effective) == 1:
		((key, val),) = effective.items()
		setattr(args, key, val)

def compression_cmd(
		option: Union[None, bool, str], 
		ini: ConfigParser, section: str,
		bool_key: str, str_key: str, other_key: str,
		default: Sequence[str],
		fallback: Optional[Sequence[str]] = None) \
		-> Optional[Sequence[str]]:
	if option is False:
		return None
	elif isinstance(option, str):
		return shlex.split(option)
	elif option is None and ini.has_option(section, bool_key):
		option = ini.getboolean(section, bool_key)
		if not option:
			return None

	assert option in (None, True)
	if ini.has_option(section, str_key):
		return shlex.split(ini.get(section, str_key))
	elif option is True:
		return default
	elif ini.has_option(section, other_key):
		return default
	else:
		return fallback

def add_common_flags(parser: argparse.ArgumentParser,
			with_uuid: bool = False) -> None:
	parser.add_argument("--no-color", dest="color", action="store_false",
				default=None)
	parser.add_argument("--show-uuid", "-u", action="store_true",
				default=None)
	if with_uuid:
		parser.add_argument("--uuid", "-U", action="store_true")

	parser.add_argument("--config", "-c", type=str)
	parser.add_argument("--section", "-C", type=str)

	mutex = parser.add_mutually_exclusive_group()
	mutex.add_argument("--service-account-info", type=str)
	mutex.add_argument("--service-account-info-file", "-S", type=str)
	mutex.add_argument("--service-account-info-command", type=str)

	mutex = parser.add_mutually_exclusive_group()
	mutex.add_argument("--bucket-name", "-b", type=str, dest="bucket")
	mutex.add_argument("--bucket-label", "-B", type=str, action="append")
	parser.add_argument("--prefix", "-p", type=str)

# Main starts here.
# Parse the command line.
parser = argparse.ArgumentParser()
subcommands = parser.add_subparsers(required=True, dest="subcommand")

# list buckets/local/remote
parser_list = subcommands.add_parser("list")
subparser = parser_list.add_subparsers(required=True, dest="subsubcommand")

parser_list_buckets = subparser.add_parser("buckets")
add_common_flags(parser_list_buckets)
parser_list_buckets.add_argument("dir", nargs='?')

parser_list_local = subparser.add_parser("local")
add_common_flags(parser_list_local)
parser_list_local.add_argument("--check-remote", "-r", action="store_true")
parser_list_local.add_argument("dir", nargs='?', default='.')

parser_list_remote = subparser.add_parser("remote")
add_common_flags(parser_list_remote)
parser_list_remote.add_argument("dir", nargs='?')

# delete local/remote
parser_delete = subcommands.add_parser("delete")
subparser = parser_delete.add_subparsers(required=True, dest="subsubcommand")

parser_delete_local = subparser.add_parser("local")
add_common_flags(parser_delete_local, with_uuid=True)
parser_delete_local.add_argument("--dry-run", "-n", action="store_true")
parser_delete_local.add_argument("--all", "-a", action="store_true")
mutex = parser_delete_local.add_mutually_exclusive_group()
mutex.add_argument("--first", action="store_true")
mutex.add_argument("--from", type=str, dest="frm")
mutex = parser_delete_local.add_mutually_exclusive_group()
mutex.add_argument("--last", action="store_true")
mutex.add_argument("--to", type=str)
parser_delete_local.add_argument("--exact", "-x", type=str,
					nargs='+', default=())
mutex = parser_delete_local.add_mutually_exclusive_group()
mutex.add_argument("--force", action="store_true")
mutex.add_argument("--force-all", action="store_true")
parser_delete_local.add_argument("dir", nargs='?', default='.')

parser_delete_remote = subparser.add_parser("remote")
add_common_flags(parser_delete_remote, with_uuid=True)
parser_delete_remote.add_argument("--dry-run", "-n", action="store_true")
parser_delete_remote.add_argument("--all", "-a", action="store_true")
mutex = parser_delete_remote.add_mutually_exclusive_group()
mutex.add_argument("--first", action="store_true")
mutex.add_argument("--from", type=str, dest="frm")
mutex = parser_delete_remote.add_mutually_exclusive_group()
mutex.add_argument("--last", action="store_true")
mutex.add_argument("--to", type=str)
parser_delete_remote.add_argument("--exact", "-x", type=str,
					nargs='+', default=())
mutex = parser_delete_remote.add_mutually_exclusive_group(required=True)
mutex.add_argument("--delete-full", action="store_true")
mutex.add_argument("--delete-delta", action="store_true")
mutex.add_argument("--delete-delta-broken", action="store_true")
mutex.add_argument("--delete-full-delta", action="store_true")
mutex.add_argument("--delete-delta-full", action="store_true")
mutex = parser_delete_remote.add_mutually_exclusive_group()
mutex.add_argument("--force", action="store_true")
mutex.add_argument("--force-all", action="store_true")
parser_delete_remote.add_argument("dir", nargs='?', default='.')

# upload/download
for subcommand in ("upload", "download"):
	cmd = subcommands.add_parser(subcommand)
	add_common_flags(cmd, with_uuid=True)

	if subcommand == "upload":
		cmd.add_argument("--reupload", action="store_true")

	mutex = cmd.add_mutually_exclusive_group()
	mutex.add_argument("--first", action="store_true")
	mutex.add_argument("--from", type=str, dest="frm")
	cmd.add_argument("--to", type=str)
	cmd.add_argument("--exact", "-x", type=str, nargs='+', default=())

	mutex = cmd.add_mutually_exclusive_group()
	mutex.add_argument("--prefer-delta", "-d", action="store_true",
				default=None)
	mutex.add_argument("--force-delta", "-D", action="store_true",
				default=None)
	mutex.add_argument("--prefer-full", "-f", action="store_true",
				default=None)
	mutex.add_argument("--force-full", "-F", action="store_true",
				default=None)

	mutex = cmd.add_mutually_exclusive_group()
	mutex.add_argument("--autodelete", "-A", action="store_true",
				default=None)
	mutex.add_argument("--no-autodelete",
				dest="autodelete", action="store_false",
				default=None)

	mutex = cmd.add_mutually_exclusive_group()
	mutex.add_argument("--dry-run", "-n", action="store_true")
	mutex.add_argument("--wet-run", "-N", action="count", default=0)
	cmd.add_argument("--force-wet-run", "-W", action="store_true")

	mutex = cmd.add_mutually_exclusive_group()
	if subcommand == "upload":
		mutex.add_argument("--compress", "-Z",
					dest="compress", action="store_true",
					default=None)
		mutex.add_argument("--no-compress",
					dest="compress", action="store_false",
					default=None)
		mutex.add_argument("--compressor", dest="compress")
	else:
		mutex.add_argument("--decompress", "-Z",
					dest="compress", action="store_true",
					default=None)
		mutex.add_argument("--no-decompress", "--no-compress",
					dest="compress", action="store_false",
					default=None)
		mutex.add_argument("--decompressor", dest="compress")

	mutex = cmd.add_mutually_exclusive_group()
	mutex.add_argument("--uncompressed-index",
				dest="compress_index", action="store_false",
				default=None)
	if subcommand == "upload":
		mutex.add_argument("--index-compressor",
					dest="compress_index")
	else:
		mutex.add_argument("--index-decompressor",
					dest="compress_index")

	mutex = cmd.add_mutually_exclusive_group()
	if subcommand == "upload":
		mutex.add_argument("--no-encrypt",
					dest="encrypt", action="store_false",
					default=None)
		mutex.add_argument("--encryption-command", "--encrypt")
	else:
		mutex.add_argument("--no-decrypt", "--no-encrypt",
					dest="encrypt", action="store_false",
					default=None)
		mutex.add_argument("--decryption-command", "--decrypt")
	mutex.add_argument("--encryption-key", "--key")
	mutex.add_argument("--encryption-key-command", "--key-cmd")
	cmd.add_argument("--cleartext-index", action="store_false")

	cmd.add_argument("--no-header", action="store_false",
				dest="header", default=None)
	cmd.add_argument("--no-verify-blob-size",
				dest="verify_blob_size", action="store_false",
				default=None)

	if subcommand == "upload":
		cmd.add_argument("--upload-chunk-size", type=int)
	cmd.add_argument("--progress", type=int)
	cmd.add_argument("--timeout", type=int)

	cmd.add_argument("dir", nargs='?')

args = parser.parse_args()
if hasattr(args, "subsubcommand"):
	# Make it easier to switch based on @args.subcommand.
	args.subcommand = f"{args.subcommand} {args.subsubcommand}"

if args.subcommand in ("upload", "download"):
	if (args.first or args.frm is not None or args.to is not None) \
			and args.exact:
		parser.error("cannot specify --exact "
				"with --first/--from/--to")
	if args.uuid:
		# Convert selectors to UUIDs.
		if args.frm is not None:
			args.frm = uuid.UUID(args.frm)
		if args.to is not None:
			args.to = uuid.UUID(args.to)
		for i, exact in enumerate(args.exact):
			args.exact[i] = uuid.UUID(exact)
	else:	# Make --from/--to/--exact basenames and verify they all
		# reside in the same directory.
		dirs = set()
		if args.dir is not None:
			dirs.add(args.dir)
		if args.frm is not None:
			d, args.frm = os.path.split(args.frm)
			dirs.add(d or '.')
		if args.to is not None:
			d, args.to = os.path.split(args.to)
			dirs.add(d or '.')
		for i, exact in enumerate(args.exact):
			d, args.exact[i] = os.path.split(exact)
			dirs.add(d or '.')

		def stat(path):
			sbuf = os.stat(path)
			return sbuf.st_dev, sbuf.st_ino
		if len(dirs) > 1 and len(set(stat(d) for d in dirs)) > 1:
			parser.error("conflicting directories")
		if args.dir is None and dirs:
			# Choose randomly.
			args.dir = dirs.pop()
	if args.dir is None:
		args.dir = '.'

config = find_config_file(args)
if config is not None:
	# Load @config and merge into @args.
	ini = ConfigParser()
	try:
		if not ini.read(config):
			sys.exit(f"{config}: config file not found")
	except configparser.Error as ex:
		sys.exit(f"{config}: {ex}")

	section = args.section if args.section is not None else "default"

	add_options_from_ini(args, ini, section, "color", tpe=bool)
	add_options_from_ini(args, ini, section, "show_uuid", tpe=bool)

	add_options_from_ini(args, ini, section,
				"service_account_info",
				"service_account_info_file",
				"service_account_info_command")
	if args.service_account_info is not None:
		args.service_account_info = ini.as_dict(
			args.service_account_info)

	add_options_from_ini(args, ini, section, "bucket", "bucket_label")
	if isinstance(args.bucket_label, str):
		# Prepare it for parse_labels().  We don't need to be fancy
		# because label values can't contain special characters in GCS.
		args.bucket_label = re.split(r",\s*", args.bucket_label)
	add_options_from_ini(args, ini, section, "prefix")

	if args.subcommand in ("upload", "download"):
		add_options_from_ini(args, ini, section,
					"prefer_delta", "force_delta",
					"prefer_full", "force_full",
					tpe=bool)
		add_options_from_ini(args, ini, section, "autodelete",
					tpe=bool)

		if args.subcommand == "upload":
			args.compress = compression_cmd(
					args.compress,
					ini, section,
					"compress",
					"compressor", "decompressor",
					DFLT_COMPRESSOR)
			args.compress_index = compression_cmd(
					args.compress_index,
					ini, section,
					"compress-index",
					"index-compressor",
					"index-decompressor",
					DFLT_COMPRESSOR,
					DFLT_COMPRESSOR)
		else:
			args.compress = compression_cmd(
					args.compress,
					ini, section,
					"compress",
					"decompressor", "compressor",
					DFLT_DECOMPRESSOR)
			args.compress_index = compression_cmd(
					args.compress_index,
					ini, section,
					"compress-index",
					"index-decompressor",
					"index-compressor",
					DFLT_DECOMPRESSOR,
					DFLT_DECOMPRESSOR)

		if args.encrypt is False:
			# Ignore encryption options in @ini, even if they are
			# conflicting.
			pass
		elif args.subcommand == "upload":
			add_options_from_ini(args, ini, section,
				"encryption_command",
				"encryption_key",
				"encryption_key_command")
			if args.encryption_command is not None:
				args.encrypt = True
				args.encryption_command = \
					shlex.split(args.encryption_command)
		else:
			add_options_from_ini(args, ini, section,
				"decryption_command",
				"encryption_key",
				"encryption_key_command")
			if args.decryption_command is not None:
				args.encrypt = True
				args.decryption_command = \
					shlex.split(args.decryption_command)
		if args.encrypt is not None:
			pass
		elif args.encryption_key is not None:
			args.encrypt = True
			args.encryption_key = base64.b64decode(
					args.encryption_key, validate=True)
		elif args.encryption_key_command is not None:
			args.encrypt = True
			args.encryption_key_command = \
				shlex.split(args.encryption_key_command)

		add_options_from_ini(args, ini, section, "header", tpe=bool)
		add_options_from_ini(args, ini, section, "verify_blob_size",
								tpe=bool)

		add_options_from_ini(args, ini, section, "upload_chunk_size",
								tpe=int)
		add_options_from_ini(args, ini, section, "progress", tpe=int)
		add_options_from_ini(args, ini, section, "timeout", tpe=int)
elif args.service_account_info is not None:
	parser.error("--service-account-info requires a config file, "
			"but none was found")

# Postprocess @args.
if args.show_uuid is None and hasattr(args, "uuid"):
	args.show_uuid = args.uuid

if args.service_account_info_command is not None:
	args.service_account_info_command = shlex.split(
		args.service_account_info_command)

if (args.subcommand in ("list remote", "delete remote", "upload", "download")
		or (args.subcommand == "list local" and args.check_remote)
		or (args.subcommand == "delete local" and not args.force_all)):
	if args.bucket is None and args.bucket_label is None:
		parser.error("either of --bucket-name or --bucket-label "
				"is required")

if args.subcommand in ("delete local", "delete remote"):
	has_from = args.first or args.frm is not None
	has_to = args.last or args.to is not None
	if has_from and not has_to:
		parser.error("either --to or --last is required")
	elif has_to and not has_from:
		parser.error("either --first or --from is required")
	elif args.all and (has_from or has_to or args.exact):
		parser.error("cannot specify --all "
				"with --first/--from/--to/--last/--exact")
	elif args.exact and (args.all or has_from or has_to):
		parser.error("cannot specify --exact "
				"with --all/--first/--from/--to/--last")
	elif not args.all and not has_from and not has_to and not args.exact:
		parser.error("either --first/--from and --to/--last "
				"or --exact/--all is required")
	if args.all:
		args.first = args.last = True

if args.subcommand == "delete remote":
	if args.delete_delta_broken and (args.force or args.force_all):
		parser.error("--force/--force-all doesn't make sense with "
				"--delete-delta-broken")
	elif args.delete_delta_full and not (args.force or args.force_all):
		parser.error("--delete-delta-full doesn't make sense without "
				"--force or --force-all")
	elif args.delete_full_delta and not (args.force or args.force_all):
		# This is like --delete-full --delete-delta-broken.
		pass

if args.subcommand == "upload":
	if args.reupload and args.force_wet_run:
		# --force-wet-run ignores remote backups.
		parser.error("--reupload doesn't make sense "
				"with --force-wet-run")
	if args.upload_chunk_size is not None and args.upload_chunk_size <= 0:
		parser.error(
			f"--upload-chunk-size ({args.upload_chunk_size}) "
			"must be positive")

if args.subcommand == "download" and args.autodelete \
		and (args.first or args.frm is not None or args.exact):
	# --first/--from/--exact imply we don't want to delete the selected
	# backups.
	parser.error("cannot specify --autodelete "
			"with --first/--from/--exact")

if args.subcommand in ("upload", "download"):
	# Set defaults.
	if args.force_wet_run and not args.wet_run:
		args.wet_run = 1
	if args.header is None:
		args.header = args.encrypt
	if args.verify_blob_size is None:
		args.verify_blob_size = args.encrypt
	if args.progress is None:
		args.progress = 30
	elif args.progress < 0:
		parser.error(f"--progress ({args.progress}) "
				"must be non-negative")

if args.show_uuid:
	Snapshot.include_uuid_in_fmt = True
if args.color is None:
	args.color = os.isatty(sys.stdout.fileno())
if args.color:
	Snapshot.emphasize_uuid_in_fmt = True

# Run
try:
	if args.subcommand == "list buckets":
		cmd_list_buckets(args)
	elif args.subcommand == "list local":
		cmd_list_local(args)
	elif args.subcommand == "list remote":
		cmd_list_remote(args)
	elif args.subcommand == "delete local":
		cmd_delete_local(args)
	elif args.subcommand == "delete remote":
		cmd_delete_remote(args)
	elif args.subcommand == "upload":
		cmd_upload(args)
	elif args.subcommand == "download":
		cmd_download(args)
except KeyboardInterrupt:
	sys.exit("Interrupted.")
except (FatalError, UserError) as ex:
	sys.exit("%s: %s." % (type(ex).__name__, " ".join(ex.args)))

# vim: set foldmethod=marker:
# End of giccs.py
