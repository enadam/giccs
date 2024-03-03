#!/usr/bin/python3
#
# TODO: {{{
# blob uuid:
#	protected: none (from signature)
#	encrypted: none (from blob name)
# blob type:
#	protected: none (from blob name)
#	encrypted: encrypted
# subvolume:
#	protected: string
#	encrypted: encrypted
# snapshot name:
#	protected: none (from blob name)
#	encrypted: encrypted
# snapshot uuid:
#	protected: string
#	encrypted: encrypted
# parent uuid:
#	protected: string
#	encrypted: encrypted
# expected size:
#	protected: string
#	encrypted: encrypted
# signature:
#	protected: encrypted hash of all other metadata
#	encrypted: none
#
# delete local/remote --flush (--delete-full-delta --force-all)
# consistency check of remote backups
#
# upload/download: split plan and execution
# consider using clone sources when uploading
#
# document max blob size (5 TiB)
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
# external encryption must generate and verify the MAC
# }}}

# Modules {{{
from typing import	TypeVar, Final, Protocol, \
			Any, Union, Optional, \
			Generator, Iterable, Callable, \
			Container, Collection, Sequence, \
			BinaryIO, ByteString

import sys, os
import io, fcntl
import subprocess
import time, datetime
import re, bisect, uuid
import base64, binascii
import random, secrets
import argparse, configparser
import enum, dataclasses, struct
import contextlib

import btrfs

import google.cloud.storage
import google.oauth2.service_account
# }}}

# Constants and structures {{{
# Make sure the child IntEnum's values are within bounds.
class EnumGuard:
	def width(self):
		return 4

	def __init__(self, value):
		assert 0 <= value < 1 << self.width()

# (Backup UUID, BlobType, EncryptedDataType) should uniquely identify
# an encrypted piece of data.  By prepending them to the cleartext and
# verifying them during decryption we ensure that the ciphertext wasn't
# replaced with another surreptitiously.
class EncryptedDataType(EnumGuard, enum.IntEnum):
	PAYLOAD	= 0
	SIZE	= 1

# (Backup UUID, BlobType) should uniquely identify a blob.
@enum.unique
class BlobType(EnumGuard, enum.IntEnum):
	INDEX	= 0
	FULL	= 1
	DELTA	= 2

	def data_type_id(self, data_type: EncryptedDataType) -> int:
		return self.value << self.width() | data_type

# A cached singleton.
UUID0 = uuid.UUID(int=0)

# We store btrfs volume UUIDs in uuid.UUID, so it's important that they
# have the same size.
BTRFS_UUID_SIZE = 16
assert len(UUID0.bytes) == BTRFS_UUID_SIZE

BTRFS_VOL_NAME_MAX = 255
btrfs_ioctl_get_subvol_info_args_st: Final[struct.Struct] = struct.Struct(
	"=Q%dsQQQQ" % (BTRFS_VOL_NAME_MAX + 1)
	+ ("%ds" % BTRFS_UUID_SIZE) * 3
	+ "4Q"
	+ "QI4x" * 4
	+ "8Q")
BTRFS_IOC_GET_SUBVOL_INFO = btrfs.ioctl._IOR(
				btrfs.ioctl.BTRFS_IOCTL_MAGIC, 60,
				btrfs_ioctl_get_subvol_info_args_st)

BTRFS_SUBVOL_NAME_MAX = 4039
btrfs_ioctl_vol_args_v2_st: Final[struct.Struct] = struct.Struct(
	"="
	+ "8x" * 3
	+ "8x" * 4
	+ "%ds" % (BTRFS_SUBVOL_NAME_MAX + 1))
BTRFS_IOC_SNAP_DESTROY_V2 = btrfs.ioctl._IOW(
				btrfs.ioctl.BTRFS_IOCTL_MAGIC, 63,
				btrfs_ioctl_vol_args_v2_st)

# Header for non-InternalCipher encryption.
encryption_header_st: Final[struct.Struct] = \
	struct.Struct(f"B{BTRFS_UUID_SIZE}s")
# }}}

# Exceptions {{{
GoogleAPICallError = google.api_core.exceptions.GoogleAPICallError
def parse_GoogleAPICallError(ex: GoogleAPICallError) -> str:
	error = [ ex.code.name ]
	if ex.response is None:
		return error[0]

	from requests.exceptions import JSONDecodeError

	try:
		js = ex.response.json()
	except JSONDecodeError:
		error.append(ex.response.text)
	else:
		if isinstance(js, dict) and "error" in js:
			js = js["error"]
			if isinstance(js, dict):
				msg = js.get("message")
				if msg is not None:
					error.append(msg)

	return ": ".join(error)

# Bad user input.
class UserError(Exception): pass

# Any other non-recoverable error.
class FatalError(Exception): # {{{
	def __init__(self, *args):
		# Dig the detailed error message out of GoogleAPICallError.
		if len(args) == 1 and isinstance(args[0], GoogleAPICallError):
			args = (parse_GoogleAPICallError(args[0]),)
		super().__init__(*args)
# }}}

# Possible foul-play detected.
class SecurityError(FatalError): pass

# System is in unexpected state.
class ConsistencyError(FatalError): pass
# }}}

# Command line parsing {{{
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

	def as_dict(self, section: str) -> dict[str, str]:
		return dict(self.items(section))
# }}}

# Represents the command line options of a single subcommand.
class CmdLineOptions: # {{{
	# Thrown during parsing the command line.
	class CmdLineError(UserError): pass

	# A group of related command line options, which are displayed
	# together in the help text.
	class Section:
		# Passed to ArgumentParser.add_argument_group().
		name: Optional[str]

		# The options to add to the argument group.
		options: list[Union[tuple[Sequence[str], dict[str, Any]], "Mutex"]]

		def __init__(self, name: Optional[str] = None):
			self.name = name
			self.options = [ ]

		# Called by subclasses of CmdLineOptions to add
		# mutually-exclusive options.
		def add_mutually_exclusive_group(self, required=False) -> "Mutex":
			mutex = CmdLineOptions.Mutex(required)
			self.options.append(mutex)
			return mutex

		# Called by subclasses of CmdLineOptions to find the last
		# Mutex group in @self.options.
		def last_mutex(self) -> "Mutex":
			return next(
				opt for opt in reversed(self.options)
				if isinstance(opt, CmdLineOptions.Mutex))

		# Called by subclasses of CmdLineOptions to add a command-line
		# argument to @self.options.
		def add_argument(self, *flags, **kw) -> None:
			self.options.append((flags, kw))

		def add_int_argument(self, *flags, **kw) -> None:
			self.add_argument(*flags, type=int, **kw)

		def add_enable_flag(self, *flags, **kw) -> None:
			self.add_argument(*flags, **kw, action="store_true")

		def add_enable_flag_no_dflt(self, *flags, **kw) -> None:
			self.add_enable_flag(*flags, **kw, default=None)

		def add_disable_flag(self, *flags, **kw) -> None:
			if "dest" not in kw:
				kw["dest"] = flags[0].removeprefix("--no-") \
							.replace('-', '_')
			self.add_argument(*flags, **kw, action="store_false")

		def add_disable_flag_no_dflt(self, *flags, **kw) -> None:
			self.add_disable_flag(*flags, **kw, default=None)

		# Called by CmdLineOptions.add_arguments() to add @self.options
		# to @parser.
		def add_arguments(self, parser: argparse.ArgumentParser) \
					-> None:
			if not self.options:
				return

			if self.name is not None:
				parser = parser.add_argument_group(self.name)

			for opt in self.options:
				if isinstance(opt, CmdLineOptions.Mutex):
					opt.add_arguments(parser)
				else:
					flags, kw = opt
					parser.add_argument(*flags, **kw)

	# A group of mutually exclusive command line options.
	class Mutex(Section):
		# Passed to ArgumentParser.add_mutually_exclusive_group().
		required: bool

		def __init__(self, required: bool = False):
			super().__init__()
			self.required = required

		# Called by Section.add_arguments().
		def add_arguments(self, parser: argparse.ArgumentParser) \
					-> None:
			mutex = parser.add_mutually_exclusive_group(
					required=self.required)
			for flags, kw in self.options:
				mutex.add_argument(*flags, **kw)

	# The default --config.
	CONFIG_FILE = "giccs.conf"

	# The argument groups we may add to argparse.ArgumentParser if they
	# have command line options.
	sections: dict[str, Section]

	# The positional argument.  Can be set by pre_validate() of subclasses.
	dir: Optional[str] = None

	# Set by override_flags() and used by __getattribute__().
	_overrides: Optional[dict[str, Any]] = None

	ini: Optional[ConfigParser] = None
	config_file: Optional[str] = None
	config_section: str = "default"

	def __init__(self):
		 # In order to make the most sense in --help, we will add the
		 # argument groups in this order, relying on dict preserving
		 # the insertion order.
		self.sections = { }
		for key, title in (
			("common",	"Common options"		),
			("display",	"Display options"		),
			("config",	"Config file options"		),
			("account",	"Account configuration"		),
			("bucket",	"Bucket and blob selection"	),
			("snapshot",	"Snapshot selection"		),
			("backup",	"Backup selection"		),
			("rmdelete",	"Which backups to delete"	),
			("indexsel",	"Index selection"		),
			("upload",	"Backup options"		),
			("download",	"Restore options"		),
			("index",	"Indexing"			),
			("compress",	"Compression"			),
			("encryption",	"Encryption"			),
			("transfer",	"Transfer options"		),
			("autodel",	"Autodeletion"			),
			("force",	"Safety options"		),
			("operation",	"Operation"			),
			("other",	"Other options"			),
			("positional",	"Positional arguments"		),
		):
			self.sections[key] = self.Section(title)
		self.declare_arguments()

	def __getattribute__(self, attr):
		if attr != "_overrides" \
				and self._overrides is not None \
				and attr in self._overrides:
			return self._overrides[attr]
		return super().__getattribute__(attr)

	# Must be implemented by subclasses to add options to @self.sections.
	def declare_arguments(self) -> None:
		pass

	# Must be overridden and invoked by subclasses to validate @args
	# and update @self before load_config().
	def pre_validate(self, args: argparse.Namespace) -> None:
		# We don't have the attribute if add_dir() wasn't called.
		if getattr(args, "dir", None) is not None:
			self.dir = args.dir

	# Must be implemented by subclasses to validate @args and update @self
	# after load_config().
	def post_validate(self, args: argparse.Namespace) -> None:
		pass

	# Private methods.
	# Search for a config file in:
	# * --config (@self.config_file)
	# * $GICCS_CONFIG
	# * @self.dir or .
	# * $HOME
	# * /etc
	def find_config_file(self) -> Optional[str]:
		if self.config_file is not None:
			return self.config_file

		config = os.environ.get("GICCS_CONFIG")
		if config is not None:
			return config

		dot_config = f".{self.CONFIG_FILE}"
		if self.dir is not None and self.dir != '.':
			config = os.path.join(self.dir, dot_config)
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

		config = os.path.join("/etc", self.CONFIG_FILE)
		if os.path.exists(config):
			return config

		return None

	# Initialize @self.ini.
	def load_config(self):
		config = self.find_config_file()
		if config is None:
			return

		ini = ConfigParser()
		try:
			if not ini.read(config):
				raise self.CmdLineError(
					f"{config}: config file not found")
		except configparser.Error as ex:
			raise FatalError(f"{config}: {ex}") from ex
		else:
			self.ini = ini

	# Called by subclasses to add the positional argument.
	def add_dir(self, default=True) -> None:
		if default:
			self.dir = '.'
		self.sections["positional"].add_argument("dir", nargs='?')

	# If none of the @options are in @args, find the one set in @self.ini
	# and move it to @args.
	def merge_options_from_ini(
			self, args: argparse.Namespace,
			*options: Sequence[str], tpe: type = str) -> None:
		if self.ini is None:
			return

		# Were any of the @options specified through the command line?
		for key in options:
			if getattr(args, key, None) is not None:
				# Don't even look at @self.ini.  It is assumed
				# that only one option is set in @args.
				return

		# Collect options set in the @default and @non_default sections
		# of @self.ini.
		default = { }
		non_default = { }
		for key in options:
			try:
				val = self.ini.get(self.config_section, key)
			except configparser.NoSectionError as ex:
				raise self.CmdLineError(
					"%s: %s"
					% (self.ini.filenames[0],
						ex.message)) from ex
			except configparser.NoOptionError:
				continue

			# @lst to add @val.
			lst = default if self.ini.is_default(val) \
					else non_default

			# Get the right @val based on @tpe.
			if tpe is bool:
				val = self.ini.getboolean(
						self.config_section, key)
			elif tpe is int:
				val = self.ini.getint(
						self.config_section, key)

			lst[key] = val

		# Verify that the @default or @non_default section doesn't
		# have conflicting (more than one) options.  It's OK to have
		# one in the @default section being overridden by another in
		# the @non_default.
		effective = non_default or default
		if len(effective) > 1:
			raise self.CmdLineError(
				"%s: conflicting options in section %s: %s"
				% (self.ini.filenames[0], self.config_section,
					", ".join(effective.keys())))
		elif len(effective) == 1:
			((key, val),) = effective.items()
			setattr(args, key, val)

	# Verify that @val is positive.
	def positive(self,
			flag: str, val: Optional[int],
			default: Optional[int] = None) \
			-> Optional[int]:
		if val is None:
			return default
		if val <= 0:
			raise self.CmdLineError(
				f"{flag} ({val}) must be positive")
		return val

	# Split @s with shlex.split().
	def shlex_split(self, what: str, s: str) -> list[str]:
		import shlex

		try:
			return shlex.split(s)
		except ValueError as ex:
			raise self.CmdLineError(
					"%s: %s"
					% (what.replace('_', '-'), ex.args[0]))

	# Public methods.
	# Add the options declared in @self.sections to @parser.
	def add_arguments(self, parser: argparse.ArgumentParser) -> None:
		for section in self.sections.values():
			section.add_arguments(parser)

	# Set up the object state from command-line arguments.
	def setup(self, args: argparse.Namespace) -> None:
		self.pre_validate(args)
		self.load_config()
		self.post_validate(args)

	@contextlib.contextmanager
	def override_flags(self, **overrides):
		prev_overrides = self._overrides
		if prev_overrides is not None:
			overrides = { **prev_overrides, **overrides }

		self._overrides = overrides
		yield
		self._overrides = prev_overrides
# }}}

# Represents a top-, sub- or leaf-level command, which may also have
# CmdLineOptions.
class CmdLineCommand(CmdLineOptions): # {{{
	cmd: str
	help: str
	description: Optional[str] = None

	_subcommands: Optional[Sequence["CmdLineCommand"]] = None

	def get_subcommands(self) -> Sequence["CmdLineCommand"]:
		# By default commands don't have subcommands.
		return ()

	@property
	def subcommands(self) -> Sequence["CmdLineCommand"]:
		# Memoize self.get_subcommands(), so we have a single instance
		# of subcommands.
		if self._subcommands is None:
			self._subcommands = self.get_subcommands()
		return self._subcommands

	def find_subcommand(self, cmd: str) -> "CmdLineCommand":
		for subcommand in self.subcommands:
			if subcommand.cmd == cmd:
				return subcommand
		raise KeyError(f"{cmd}: subcommand not found")

	def add_arguments(self, parser: argparse.ArgumentParser) -> None:
		# Add --help to all levels of subcommands, but don't include
		# it in the help text itself.
		parser.add_argument("--help", "-h",
			action="help", help=argparse.SUPPRESS)
		super().add_arguments(parser)

	def build_for_subparser(self, subparser, level: int = 1) -> None:
		self.build_for_parser(
				subparser.add_parser(
					self.cmd,
					help=self.help,
					description=self.description,
					add_help=False),
				level)

	def build_for_parser(self,
				parser: argparse.ArgumentParser,
				level: int = 1) -> None:
		self.add_arguments(parser)

		if not self.subcommands:
			return

		subparser = parser.add_subparsers(
					required=True,
					metavar="subcommand",
					dest=f"sub{level}command")
		for subcommand in self.subcommands:
			subcommand.build_for_subparser(
					subparser, level + 1)

	def setup(self, args: argparse.Namespace) -> None:
		# Should only be called on leaf-level subcommands.
		assert not self.subcommands
		super().setup(args)

	def execute(self) -> None:
		# Leaf-level subcommand must implement it.
		raise NotImplementedError
# }}}

# Add options common to leaf-level commands.
class CmdLeaf(CmdLineCommand): # {{{
	debug: Optional[bool] = None

	def __init__(self):
		super().__init__()

		# Initialize @self.debug from the environment.
		debug = os.environ.get("GICCS_DEBUG")
		if debug is None:
			return

		try:
			self.debug = int(debug) > 0
		except ValueError:
			debug = debug.lower()
			if debug in ("true", "yes", "on"):
				self.debug = True
			elif debug in ("false", "no", "off"):
				self.debug = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["common"]
		section.add_enable_flag_no_dflt("--debug")

	def pre_validate(self, args: argparse.Namespace) -> None:
		# Enable debugging as early as possible.
		if args.debug is not None:
			self.debug = args.debug
		super().pre_validate(args)

	def post_validate(self, args: argparse.Namespace) -> None:
		# Likewise.
		self.merge_options_from_ini(args, "debug", tpe=bool)
		if self.debug is None and args.debug is not None:
			self.debug = args.debug

		super().post_validate(args)
# }}}

# Add --show-uuid and --no-color.
class ShowUUIDOptions(CmdLineOptions): # {{{
	color: bool = True
	show_uuid: Optional[bool] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["display"]
		section.add_disable_flag_no_dflt("--no-color")

		# If we wouldn't add --uuid, add it as an alias to --show-uuid.
		flags = [ "--show-uuid" ]
		if not isinstance(self, SelectionOptions):
			flags.append("--uuid")
		section.add_enable_flag_no_dflt(*flags, "-u")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args, "color", tpe=bool)
		if args.color is not None:
			self.color = args.color
		else:
			self.color = os.isatty(sys.stdout.fileno())
		if self.color:
			Snapshot.emphasize_uuid_in_fmt = True

		self.merge_options_from_ini(args, "show_uuid", tpe=bool)
		self.show_uuid = args.show_uuid
		if self.show_uuid:
			Snapshot.include_uuid_in_fmt = True
# }}}

# Add --config and --section.  The config is actually loaded by CmdLineOptions.
class ConfigFileOptions(CmdLineOptions): # {{{
	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["config"]
		section.add_argument("--config", "-c")
		section.add_argument("--section", "-C")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		if args.config is not None:
			self.config_file = args.config
		if args.section is not None:
			self.config_section = args.section
# }}}

# Obtain @service_account_info from various sources.
class AccountOptions(ConfigFileOptions): # {{{
	service_account_info: Optional[dict[str, str]] = None

	gcs_client: Optional[google.cloud.storage.Client] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		mutex = self.sections["account"].add_mutually_exclusive_group()
		mutex.add_argument("--service-account-info")
		mutex.add_argument("--service-account-info-file", "-S")
		mutex.add_argument("--service-account-info-command")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args,
					"service_account_info",
					"service_account_info_file",
					"service_account_info_command")

		if args.service_account_info is not None:
			# @self.service_account_info is a section of @self.ini.
			if self.ini is None:
				raise self.CmdLineError(
					"--service_account_info requires "
					"a --config file")
			try:
				self.service_account_info = self.ini.as_dict(
					args.service_account_info)
			except configparser.NoSectionError as ex:
				raise self.CmdLineError(
					"%s: %s"
					% (self.ini.filenames[0],
						ex.message)) from ex
			return

		# Take @self.service_account_info from a JSON?
		cmd = fin = None
		if args.service_account_info_file is not None:
			if args.service_account_info_file == '-':
				fin = sys.stdin
			else:
				fin = open(args.service_account_info_file)
		elif args.service_account_info_command is not None:
			cmdline = self.shlex_split(
					"service-account-info-command",
					args.service_account_info_command)
			cmd = subprocess.Popen(cmdline, stdout=subprocess.PIPE)
			fin = cmd.stdout
		else:	# Service account is not specified in any way.
			return

		# Read @fin and parse it as JSON.
		import json

		src = cmd.args[0] if cmd is not None else fin.name
		try:
			self.service_account_info = json.load(fin)
		except json.decoder.JSONDecodeError as ex:
			if cmd is not None:
				cmd.kill()
			raise self.CmdLineError(
					"%s: %s" % (src, ex.args[0])) from ex
		else:
			if not isinstance(self.service_account_info, dict):
				raise self.CmdLineError(f"{src}: not a dict")
		finally:
			if cmd is not None:
				wait_proc(cmd)

	# Make a google.cloud.storage.Client from @self.service_account_info.
	def get_gcs_client(self) -> google.cloud.storage.Client:
		if self.gcs_client is not None:
			return self.gcs_client

		if self.service_account_info is not None:
			creds = google.oauth2.service_account.Credentials. \
					from_service_account_info(
						self.service_account_info)
		else:
			creds = None

		self.gcs_client = google.cloud.storage.Client(
							credentials=creds)
		return self.gcs_client
# }}}

# Provide options to specify the GCS bucket to use.
class BucketOptions(AccountOptions): # {{{
	# Can be overridden by subclasses.
	bucket_required: bool = False

	bucket:		Optional[google.cloud.storage.Bucket] = None
	bucket_name:	Optional[str] = None
	bucket_labels:	Optional[dict[str, Optional[str]]] = None
	prefix:		Optional[str] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		# We can't mark the @mutex required because the options
		# may be provided through the config file.
		section = self.sections["bucket"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_argument("--bucket", "-b", dest="bucket")
		mutex.add_argument("--bucket-labels", "-B", action="append")
		section.add_argument("--prefix", "-p")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args, "bucket", "bucket_labels")
		if args.bucket is not None:
			self.bucket_name = args.bucket
			bucket_labels = None
		elif isinstance(args.bucket_labels, str):
			# bucket-label was specified in the config file,
			# parse it.  We don't need to be fancy because label
			# values can't contain special characters in GCS.
			bucket_labels = re.split(r",\s*", args.bucket_labels)
		elif args.bucket_labels is not None:
			bucket_labels = args.bucket_labels
		elif self.bucket_required:
			raise self.CmdLineError(
					"either of --bucket "
					"or --bucket-labels is required")
		else:
			bucket_labels = None

		# Parse --bucket-label.
		if bucket_labels is not None:
			self.bucket_labels = { }
			for label in bucket_labels:
				key, eq, val = label.partition('=')
				self.bucket_labels[key] = val if eq else None

		self.merge_options_from_ini(args, "prefix")
		self.prefix = args.prefix

	# Does @bucket match @self.bucket_name and/or @self.bucket_labels?
	def bucket_matches(self, bucket: google.cloud.storage.Bucket) -> bool:
		if self.bucket_name is not None \
				and bucket.name != self.bucket_name:
			return False

		if self.bucket_labels is not None:
			for key, val in self.bucket_labels.items():
				if key not in bucket.labels:
					return False
				if val is not None and bucket.labels[key] != val:
					return False

		return True

	# Find the bucket specified on the command line.
	def find_bucket(self) -> google.cloud.storage.Bucket:
		if self.bucket is not None:
			return self.bucket

		gcs = self.get_gcs_client()
		if self.bucket_name is not None:
			self.bucket = gcs.bucket(self.bucket_name)
			try:
				if not self.bucket.exists():
					raise UserError(
						f"{self.bucket_name}:",
						parse_GoogleAPICallError(ex)) \
						from ex
			except GoogleAPICallError as ex:
				raise FatalError(f"{self.bucket_name}:",
					parse_GoogleAPICallError(ex)) from ex
			return self.bucket

		found = [ ]
		for bucket in gcs.list_buckets():
			if self.bucket_matches(bucket):
				found.append(bucket)

		if not found:
			raise UserError("Bucket not found")
		elif len(found) > 1:
			raise UserError("More than one buckets found")
		else:
			self.bucket = found[0]
			return self.bucket
# }}}

# Add --dry-run.
class DryRunOptions(CmdLineOptions): # {{{
	dry_run: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		# WetRunOptions will add more options to the @mutex.
		section = self.sections["operation"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag("--dry-run", "-n")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.dry_run = args.dry_run

	# Enhanced by WetRunOptions.
	def is_dry_run(self) -> bool:
		return self.dry_run
# }}}

# Add --wet-run and --wet-run-no-data.
class WetRunOptions(DryRunOptions): # {{{
	wet_run: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		mutex = self.sections["operation"].last_mutex()
		mutex.add_enable_flag("--wet-run", "-N")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.wet_run = args.wet_run

	def is_dry_run(self) -> bool:
		return self.wet_run or super().is_dry_run()
# }}}

# Add options to select snapshots or backups with --first/--from/--to/--exact.
class SelectionOptions(ShowUUIDOptions): # {{{
	# Should be provided by subclasses.
	selection_section: str

	first:		bool = False
	frm:		Union[str, uuid.UUID, None] = None
	to:		Union[str, uuid.UUID, None] = None
	exact:		list[Union[str, uuid.UUID]]
	use_uuid:	bool = False

	def __init__(self):
		super().__init__()
		self.exact = [ ]

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections[self.selection_section]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag("--first")
		mutex.add_argument("--from", dest="frm")

		# DeleteSelectionOptions will add more options to the @mutex.
		mutex = section.add_mutually_exclusive_group()
		mutex.add_argument("--to")

		section.add_argument("--exact", "-x", nargs='+', default=())

		section.add_enable_flag("--uuid", "-U")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		if (args.first or args.frm is not None \
					or args.to is not None) \
				and args.exact:
			raise self.CmdLineError(
					"cannot specify --exact "
					"with --first/--from/--to")

		self.first = args.first

		self.use_uuid = args.uuid
		if not self.use_uuid:
			self.frm    = args.frm
			self.to     = args.to
			self.exact += args.exact
			return

		# Convert selectors to UUIDs.
		def to_uuid(flag: str, val: str) -> uuid.UUID:
			try:
				return uuid.UUID(val)
			except ValueError as ex:
				raise self.CmdLineError(
					"--%s %s: %s"
					% (flag, val, ex.args[0])) \
					from ex

		if args.frm is not None:
			self.frm = to_uuid("from", args.frm)
		if args.to is not None:
			self.to = to_uuid("to", args.to)
		for exact in args.exact:
			self.exact.append(to_uuid("exact", exact))

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		if self.show_uuid is None:
			self.show_uuid = self.use_uuid
# }}}

# Adjust @self.dir based on the local snapshots selected.
class SnapshotSelectionOptions(SelectionOptions): # {{{
	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		if self.use_uuid:
			return

		# Make --from/--to/--exact basenames and verify
		# they all reside in the same directory.
		dirs = set()
		if args.dir is not None:
			dirs.add(args.dir)
		if self.frm is not None:
			dir, self.frm = os.path.split(self.frm)
			dirs.add(dir or '.')
		if self.to is not None:
			dir, self.to = os.path.split(self.to)
			dirs.add(dir or '.')
		for i, exact in enumerate(self.exact):
			dir, self.exact[i] = os.path.split(exact)
			dirs.add(dir or '.')

		def stat(path):
			sbuf = os.stat(path)
			return sbuf.st_dev, sbuf.st_ino
		if len(dirs) > 1 and len(set(map(stat, dirs))) > 1:
			raise self.CmdLineError("conflicting directories")

		# If @args.dir is not specified explicitly,
		# override @self.dir by --from/--to/--exact.
		assert self.dir is not None
		if args.dir is None and dirs:
			# Choose one randomly.
			self.dir = dirs.pop()
# }}}

# Add --last and --all.
class DeleteSelectionOptions(SelectionOptions): # {{{
	last: bool = False

	def declare_arguments(self) -> None:
		# Insert --all at the top of the @section.
		section = self.sections[self.selection_section]
		section.add_enable_flag("--all", "-a")
		super().declare_arguments()

		# Add --last to the last @mutex of the @section.
		section.last_mutex().add_enable_flag("--last")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.last = args.last
		has_from = self.first or self.frm is not None
		has_to = self.last or self.to is not None

		if has_from and not has_to:
			raise self.CmdLineError(
				"either --to or --last is required")
		elif has_to and not has_from:
			raise self.CmdLineError(
				"either --first or --from is required")
		elif args.all and (has_from or has_to or self.exact):
			raise self.CmdLineError(
				"cannot specify --all "
				"with --first/--from/--to/--last/--exact")
		elif self.exact and (args.all or has_from or has_to):
			raise self.CmdLineError(
				"cannot specify --exact "
				"with --all/--first/--from/--to/--last")
		elif not any((args.all, has_from, has_to, self.exact)):
			raise self.CmdLineError(
				"either --first/--from and --to/--last "
				"or --exact/--all is required")

		if args.all:
			self.first = self.last = True
# }}}

# Add --orphaned.
class IndexSelectionOptions(CmdLineOptions): # {{{
	orphaned: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["indexsel"]
		section.add_enable_flag("--orphaned")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.orphaned = args.orphaned
# }}}

# Add options to specify which backups to use (delta or full).
class BackupOptions(CmdLineOptions): # {{{
	prefer_delta:	bool = False
	force_delta:	bool = False
	prefer_full:	bool = False
	force_full:	bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		if isinstance(self, CmdUpload):
			section = self.sections["upload"]
		else:
			section = self.sections["download"]

		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag_no_dflt("--prefer-delta", "-d")
		mutex.add_enable_flag_no_dflt("--force-delta", "-D")
		mutex.add_enable_flag_no_dflt("--prefer-full", "-f")
		mutex.add_enable_flag_no_dflt("--force-full", "-F")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args,
					"prefer_delta", "force_delta",
					"prefer_full", "force_full",
					tpe=bool)
		if args.prefer_delta:
			self.prefer_delta = True
		elif args.force_delta:
			self.force_delta = True
		elif args.prefer_full:
			self.prefer_full = True
		elif args.force_full:
			self.force_full = True
# }}}

# Add --autodelete.
class AutodeleteOptions(CmdLineOptions): # {{{
	autodelete: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["autodel"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag_no_dflt("--autodelete", "-A")
		mutex.add_disable_flag_no_dflt("--no-autodelete")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args, "autodelete", tpe=bool)
		if args.autodelete:
			self.autodelete = True
# }}}

# Add --compress/--decompress and --compressor/--decompressor.
class CompressionOptions(CmdLineOptions): # {{{
	DFLT_COMPRESSION	= "xz"
	DFLT_COMPRESSOR		= (DFLT_COMPRESSION, "-c")
	DFLT_DECOMPRESSOR	= (DFLT_COMPRESSION, "-dc")

	compressor:		Optional[Sequence[str]] = None
	index_compressor:	Optional[Sequence[str]] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["compress"]
		mutex = section.add_mutually_exclusive_group()
		if isinstance(self, UploadBlobOptions):
			mutex.add_enable_flag_no_dflt("--compress", "-Z")
			mutex.add_disable_flag_no_dflt("--no-compress")
			mutex.add_argument("--compressor", dest="compress")
			if isinstance(self, CmdUpload):
				mutex = section.add_mutually_exclusive_group()
				mutex.add_enable_flag_no_dflt(
						"--compress-index")
				mutex.add_disable_flag_no_dflt(
						"--no-compress-index")
				mutex.add_argument("--index-compressor",
						dest="compress_index")
		else:
			flags = [ "--decompress", "--compress", "-Z" ]
			if isinstance(self, CmdGetIndex):
				flags.insert(1, "--decompress-index")
				flags.insert(-1, "--compress-index")
			mutex.add_enable_flag_no_dflt(*flags, dest="compress")

			flags = [ "--no-decompress", "--no-compress" ]
			if isinstance(self, CmdGetIndex):
				flags.insert(1, "--no-decompress-index")
				flags.append("--no-compress-index")
			mutex.add_disable_flag_no_dflt(*flags, dest="compress")

			flags = [ "--decompressor" ]
			if isinstance(self, CmdGetIndex):
				flags.append("--index-decompressor")
			mutex.add_argument(*flags, dest="compress")

	def get_compressor(self,
			option: Union[None, bool, str], 
			bool_key: str, str_key: str, other_key: str,
			default: Sequence[str],
			fallback: Optional[Sequence[str]] = None) \
			-> Optional[Sequence[str]]:
		if option is False:
			return None
		elif isinstance(option, str):
			return self.shlex_split(str_key, option)
		elif option is None and self.ini is not None \
				and self.ini.has_option(self.config_section,
							bool_key):
			option = self.ini.getboolean(self.config_section,
							bool_key)
			if not option:
				return None

		assert option in (None, True)
		if self.ini is not None and self.ini.has_option(
						self.config_section,
						str_key):
			return self.shlex_split(str_key,
					self.ini.get(self.config_section,
							str_key))
		elif option is True:
			return default
		elif self.ini is not None and self.ini.has_option(
						self.config_section,
						other_key):
			return default
		else:
			return fallback

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		if isinstance(self, UploadBlobOptions):
			self.compressor = self.get_compressor(
					args.compress,
					"compress",
					"compressor",
					"decompressor",
					self.DFLT_COMPRESSOR)
			if isinstance(self, CmdUpload):
				self.index_compressor = self.get_compressor(
						args.compress_index,
						"compress-index",
						"index-compressor",
						"index-decompressor",
						self.DFLT_COMPRESSOR,
						self.DFLT_COMPRESSOR)
		else:
			if isinstance(self, CmdGetIndex):
				self.compressor = self.get_compressor(
						args.compress,
						"compress-index",
						"index-decompressor",
						"index-compressor",
						self.DFLT_DECOMPRESSOR,
						self.DFLT_DECOMPRESSOR)
			else:
				self.compressor = self.get_compressor(
						args.compress,
						"compress",
						"decompressor",
						"compressor",
						self.DFLT_DECOMPRESSOR)
# }}}

# Add --encryption-key, --encryption-command etc.
class EncryptionOptions(CmdLineOptions): # {{{
	cipher_command:		Optional[Sequence[str]] = None
	encryption_key:		Optional[bytes] = None
	encryption_key_command:	Optional[Sequence[str]] = None
	encryption_key_per_uuid: bool = False

	encrypt_index:		bool = True

	encrypt_metadata:	bool = False
	verify_blob_size:	bool = False
	add_header_to_blob:	bool = False

	subvolume: Optional[str] = None

	@property
	def encrypt(self) -> bool:
		return	self.cipher_command is not None \
			or self.encryption_key is not None \
			or self.encryption_key_command is not None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["encryption"]
		mutex = section.add_mutually_exclusive_group()
		if isinstance(self, UploadBlobOptions):
			mutex.add_disable_flag_no_dflt("--no-encrypt")
			mutex.add_argument("--encryption-command", "--encrypt")
			if isinstance(self, CmdUpload):
				section.add_enable_flag_no_dflt(
						"--cleartext-index")
		else:
			flags = [ "--no-decrypt", "--no-encrypt" ]
			if isinstance(self, CmdGetIndex):
				flags.append("--cleartext-index")
			mutex.add_disable_flag_no_dflt(*flags, dest="encrypt")
			mutex.add_argument("--decryption-command", "--decrypt")
		mutex.add_argument("--encryption-key", "--key")
		mutex.add_argument("--encryption-key-command", "--key-cmd")
		section.add_enable_flag_no_dflt("--encryption-key-per-uuid")

		section.add_disable_flag_no_dflt("--no-encrypt-metadata")
		section.add_disable_flag_no_dflt("--no-verify-blob-size")
		section.add_disable_flag_no_dflt("--no-blob-header")

		section.add_argument("--subvolume", "-V")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		if args.encrypt is False:
			# Disabled with --no-encrypt or --no-decrypt,
			# ignore all options, even if they are conflicting.
			return

		self.merge_options_from_ini(args, "cleartext_index", tpe=bool)
		self.encrypt_index = not getattr(args, "cleartext_index", None)
		if isinstance(self, CmdGetIndex) and not self.encrypt_index:
			# Like above.
			assert not self.encrypt
			return

		if isinstance(self, CmdUpload):
			self.merge_options_from_ini(args,
				"encryption_command",
				"encryption_key",
				"encryption_key_command")
			if args.encryption_command is not None:
				self.cipher_command = \
					self.shlex_split(
						"encryption-command",
						args.encryption_command)
		else:
			self.merge_options_from_ini(args,
				"decryption_command",
				"encryption_key",
				"encryption_key_command")
			if args.decryption_command is not None:
				self.cipher_command = \
					self.shlex_split(
						"decryption-command",
						args.decryption_command)

		if args.encryption_key is not None:
			try:
				self.encryption_key = base64.b64decode(
						args.encryption_key,
						validate=True)
			except binascii.Error as ex:
				raise self.CmdLineError(
					"encryption key is not a valid "
					"base-64 string") from ex
		elif args.encryption_key_command is not None:
			self.encryption_key_command = \
				self.shlex_split(
					"encryption-key-command",
					args.encryption_key_command)

			self.merge_options_from_ini(args,
				"encryption_key_per_uuid", tpe=bool)
			self.encryption_key_per_uuid = \
				args.encryption_key_per_uuid

		self.encrypt_index &= self.encrypt

		self.merge_options_from_ini(args, "encrypt_metadata", tpe=bool)
		if args.encrypt_metadata is not False:
			self.encrypt_metadata = self.encrypt

		# One might want to disable this because setting metadata
		# after blob creation reuires an extra permission.
		self.merge_options_from_ini(args, "verify_blob_size", tpe=bool)
		if args.verify_blob_size is not False:
			self.verify_blob_size = self.encrypt

		self.merge_options_from_ini(args, "blob_header", tpe=bool)
		if args.blob_header is not False:
			self.add_header_to_blob = self.encrypt
		elif self.encryption_key_command is None:
			# InternalEncrypt always writes a header.
			raise self.CmdLineError(
				"--no-blob-header only makes sense "
				"with --encryption-key-command")

		self.merge_options_from_ini(args, "subvolume")
		self.subvolume = args.subvolume

class EncryptedBucketOptions(BucketOptions, EncryptionOptions):
	# Initialize @self.subvolume if it hasn't been set explicitly.
	def find_bucket(self) -> google.cloud.storage.Bucket:
		bucket = super().find_bucket()

		if self.subvolume is None:
			subvolume = [ bucket.name ]
			if self.prefix is not None:
				subvolume.append(self.prefix)
			self.subvolume = '/'.join(subvolume)

		return bucket
# }}}

# Add --upload-chunk-size, --progress and --timeout.
class TransferOptions(CmdLineOptions): # {{{
	upload_chunk_size:	Optional[int] = None
	progress:		Optional[int] = None
	timeout:		Optional[int] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["transfer"]
		if isinstance(self, CmdUpload):
			section.add_int_argument("--upload-chunk-size")
		section.add_int_argument("--progress")
		section.add_int_argument("--timeout")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		if isinstance(self, CmdUpload):
			self.merge_options_from_ini(
					args, "upload_chunk_size", tpe=int)
			self.upload_chunk_size = self.positive(
							"--upload-chunk-size",
							args.upload_chunk_size)

		self.merge_options_from_ini(args, "progress", tpe=int)
		if args.progress is None:
			self.progress = 30
		elif args.progress >= 0:
			self.progress = args.progress

		self.merge_options_from_ini(args, "timeout", tpe=int)
		self.timeout = self.positive("--timeout", args.timeout)

	def get_retry_flags(self) -> dict[str, Any]:
		kwargs = { }
		if self.timeout is not None:
			kwargs["timeout"] = self.timeout
			kwargs["retry"] = google.cloud.storage.blob.DEFAULT_RETRY \
						.with_timeout(self.timeout)
		return kwargs
# }}}

# Upload/DownloadBlobOptions {{{
class UploadBlobOptions(CompressionOptions, EncryptionOptions,
			TransferOptions, WetRunOptions):
	reupload: bool = False
	ignore_remote: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["upload"]
		section.add_enable_flag("--reupload")

		section = self.sections["operation"]
		section.add_enable_flag("--ignore-remote")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.ignore_remote = args.ignore_remote
		if self.ignore_remote and not (self.dry_run or self.wet_run):
			raise self.CmdLineError(
					"--ignore-remote only makes sense "
					"with --dry-run/--wet-run")

		self.reupload = args.reupload
		if self.reupload and self.ignore_remote:
			# With --reupload the remote backups to overwrite
			# must exist.
			raise self.CmdLineError(
					"cannot specify --ignore-remote "
					"with --reupload")

class DownloadBlobOptions(CompressionOptions, EncryptionOptions,
				TransferOptions):
	pass
# }}}

class CommonOptions(EncryptedBucketOptions, AccountOptions, ConfigFileOptions):
	pass

class DeleteOptions(CommonOptions, DryRunOptions, DeleteSelectionOptions):
	pass

# Add --verbose.
class ListRemoteOptions(CommonOptions, ShowUUIDOptions): # {{{
	bucket_required = True

	verbose: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["display"]
		section.add_enable_flag("--verbose", "-v")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.verbose = args.verbose
# }}}

# Options shared between the upload and download commands.
class UploadDownloadOptions( # {{{
		CommonOptions, SelectionOptions, BackupOptions,
		AutodeleteOptions, WetRunOptions):
	bucket_required = True

	wet_run_no_data: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		mutex = self.sections["operation"].last_mutex()
		mutex.add_enable_flag("--wet-run-no-data")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.wet_run_no_data = args.wet_run_no_data
		if self.wet_run_no_data:
			self.wet_run = True
# }}}
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
			raise FatalError(
				f"{self.fname}: invalid snapshot name")

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
	blobs: list[Optional[google.cloud.storage.Blob]]

	# Parent of the delta backup.
	parent: Optional[uuid.UUID] = None

	# Used by backup_restorable().
	restorable: Optional[bool] = None

	def __init__(self, *args):
		super().__init__(*args)
		self.blobs = [ None ] * len(BlobType)

	@property
	def index(self) -> Optional[google.cloud.storage.Blob]:
		return self.blobs[BlobType.INDEX]

	@property
	def full(self) -> Optional[google.cloud.storage.Blob]:
		return self.blobs[BlobType.FULL]

	@property
	def delta(self) -> Optional[google.cloud.storage.Blob]:
		return self.blobs[BlobType.DELTA]

	# Set one of the @blobs.
	def set_blob(self, which: BlobType, blob: google.cloud.storage.Blob) \
			-> None:
		if self.blobs[which] is not None:
			raise ConsistencyError(
				"%s has duplicate %s blobs"
				% (self.uuid, which.name))
		self.blobs[which] = blob

		if which == BlobType.DELTA:
			assert self.parent is None
			if "parent" not in blob.metadata:
				raise ConsistencyError(
					"%s has no \"parent\" metadata"
					% blob.name)
			try:
				self.parent = uuid.UUID(
						blob.metadata["parent"])
			except ValueError as ex:
				raise ConsistencyError(
					"%s has invalid parent UUID"
					% blob.name) from ex

	def clear_blob(self, which: BlobType) -> None:
		self.blobs[which] = self.parent = None

	def all_blobs(self) -> Iterable[google.cloud.storage.Blob]:
		return (blob for blob in self.blobs if blob is not None)

	def any_blob(self) -> Optional[google.cloud.storage.Blob]:
		for blob in self.blobs:
			if blob is not None:
				return blob
		return None

	def orphan(self) -> bool:
		for i, blob in enumerate(self.blobs):
			if i != BlobType.INDEX and blob is not None:
				return False
		return True
# }}}

# The internal encryption and decryption classes.
class InternalCipher: # {{{
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
	header_st: Final[struct.Struct] = \
		struct.Struct(f"!QB{BTRFS_UUID_SIZE}s")

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

	data_type_id: Optional[int]
	blob_uuid: Optional[uuid.UUID]
	blob_uuid_bytes: bytes

	wrapped: Optional[BinaryIO]

	def __init__(self, key: bytes,
			data_type_id: Optional[int] = None,
			blob_uuid: Optional[uuid.UUID] = None,
			wrapped: Optional[BinaryIO] = None):
		from cryptography.hazmat.primitives.ciphers import aead

		self.key = key
		self.cipher = aead.AESGCM(key)

		self.data_type_id = data_type_id

		self.blob_uuid = blob_uuid
		self.blob_uuid_bytes = ensure_uuid(blob_uuid).bytes

		self.wrapped = wrapped

	def init(self, wrapped: Optional[BinaryIO]) -> None:
		assert self.wrapped is None
		self.wrapped = wrapped

	def mkprng(self, seed: int) -> random.Random:
		prng = random.Random()
		prng.seed(seed, version=2)
		return prng

class InternalEncrypt(InternalCipher):
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

	def __init__(self, key: bytes,
			data_type_id: int, blob_uuid: uuid.UUID,
			nonce_rng: Optional[random.Random] = None,
			wrapped: Optional[BinaryIO] = None):
		super().__init__(key, data_type_id, blob_uuid, wrapped)

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

		# Bind the ciphertext block to the UUID, preventing it
		# from being reused in another blob.
		cleartext = bytearray(self.header_st.size)
		self.header_st.pack_into(cleartext, 0,
			rnd, self.data_type_id, self.blob_uuid_bytes)

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

class InternalDecrypt(InternalCipher):
	nonce: Optional[bytearray]
	prng: Optional[random.Random]
	ciphertext: bytearray

	inbytes: int
	outbytes: int

	def __init__(self, key: bytes,
			data_type_id: Optional[int] = None,
			blob_uuid: Optional[uuid.UUID] = None,
			wrapped: Optional[BinaryIO] = None):
		super().__init__(key, data_type_id, blob_uuid, wrapped)

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
		rnd, data_type_id, blob_uuid = \
			self.header_st.unpack_from(cleartext)

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

		if self.data_type_id is None:
			self.data_type_id = data_type_id
		elif data_type_id != self.data_type_id:
			raise SecurityError(
				"Data type ID (0x%.2X) "
				"of block at offset in=%d/out=%d "
				"differs from expected (0x%.2X)"
				% (data_type_id,
					self.inbytes, self.outbytes,
					self.data_type_id))

		if self.blob_uuid is None:
			self.blob_uuid_bytes = blob_uuid
			self.blob_uuid = uuid.UUID(bytes=blob_uuid)
		elif blob_uuid != self.blob_uuid_bytes:
			blob_uuid = uuid.UUID(bytes=blob_uuid)
			raise SecurityError(
				"Snapshot UUID (%s) "
				"of block at offset in=%d/out=%d "
				"differs from expected (%s)"
				% (blob_uuid,
					self.inbytes, self.outbytes,
					self.blob_uuid))

		assert len(cleartext) > self.header_st.size
		return cleartext[self.header_st.size:]

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

class MetaCipher:
	class DataType(enum.IntEnum):
		PAYLOAD		= 0
		SIGNATURE	= 1
		SUBVOLUME	= 2
		BLOB_TYPE	= 3
		BLOB_SIZE	= 4
		SNAPSHOT_NAME	= 5
		SNAPSHOT_UUID	= 6
		PARENT_UUID	= 7

		def field(self):
			return self.name.lower()

	args: EncryptionOptions
	blob_uuid: Optional[uuid.UUID] = None

	# Shared between MetaCipher instances.  It's either the non-per-UUID
	# key, or a dict of per-UUID keys we've retrieved before, or None if
	# no key has been cached.
	key_cache: Union[dict[Optional[uuid.UUID], bytes], bytes, None] = None

	# Like InternalCipher.header_st, but for is_external() encryption.
	external_header_st: Final[struct.Struct] = \
		struct.Struct(f"B{BTRFS_UUID_SIZE}s")

	def __init__(self, args: EncryptionOptions,
			blob_uuid: Optional[uuid.UUID] = None):
		self.args = args
		if blob_uuid is not None:
			self.blob_uuid = blob_uuid

	def get_cipher_cmd_env(self) -> dict[str, str]:
		env = os.environ.copy()

		assert self.args.subvolume is not None
		env["GICCS_SUBVOLUME"] = self.args.subvolume

		if self.blob_uuid is not None:
			env["GICCS_BLOB_UUID"] = str(self.blob_uuid)

		return env

	def get_encryption_key(self) -> bytes:
		if self.args.encryption_key is not None:
			return self.args.encryption_key

		# Is the @key cached?
		key_cache = self.__class__.key_cache
		if not self.args.encryption_key_command_per_uuid:
			assert key_cache is None or isinstance(key_cache,
								bytes)
			key = key_cache
		elif key_cache is not None:
			assert isinstance(key_cache, dict)
			key = key_cache.get(self.blob_uuid)
		else:
			key = None
		if key is not None:
			return key

		# Retrieve the @key.
		assert self.args.encryption_key_command is not None
		key = subprocess.check_output(
				self.args.encryption_key_command,
				env=self.get_cipher_cmd_env())

		# Cache the @key.  This is important if the command above
		# asks for a password.
		if not self.args.encryption_key_command_per_uuid:
			self.__class__.key_cache = key
		elif key_cache is not None:
			key_cache[self.blob_uuid] = key
		else:
			self.__class__.key_cache = { self.blob_uuid: key }

		return key

	def is_internal(self) -> bool:
		return self.args.encrypt \
			and self.args.encryption_command is None

	CipherClass = TypeVar("CipherClass", bound=InternalCipher)
	def internal_cipher(self, cipher_class: CipherClass,
				data_type: DataType, wrapped: BinaryIO) \
				-> CipherClass:
		assert self.is_internal()
		return cipher_class(self.get_encryption_key(),
					data_type.value, self.blob_uuid,
					wrapped=wrapped)

	def internal_encrypt(self, data_type: DataType, src: BinaryIO) \
				-> InternalEncrypt:
		return self.internal_cipher(InternalEncrypt, data_type, src)

	def internal_decrypt(self, data_type: DataType, dst: BinaryIO) \
				-> InternalDecrypt:
		return self.internal_cipher(InternalDecrypt, data_type, dst)

	def is_external(self) -> bool:
		return self.args.encrypt \
			and self.args.encryption_command is not None

	def external(self) -> dict[str, Any]:
		assert self.is_external()
		return {
			"args": self.args.cipher_command,
			"env": self.get_cipher_cmd_env(),
		}

	def encrypt(self, data_type: DataType, cleartext: bytes) \
			-> Union[memoryview, bytearray, bytes]:
		if self.is_internal():
			return self.internal_encrypt(
					data_type,
					io.BytesIO(cleartext)).read()
		else:	# @self.args.add_header_to_blob is pointedly ignored
			# for the meaningful security of metadata.
			header = self.external_header_st.pack(
					data_type.value,
					ensure_uuid(self.blob_uuid).bytes)
			return subprocess.check_output(
					**self.external(),
					input=header + cleartext)

	def decrypt(self, data_type: DataType, ciphertext: bytes) \
			-> memoryview:
		if self.is_internal():
			cleartext = io.BytesIO()
			cipher = self.internal_decrypt(data_type, cleartext)
			cipher.write(ciphertext)
			cipher.close()

			if self.blob_uuid is None:
				self.blob_uuid = cipher.blob_uuid

			return cleartext.getbuffer()

		# is_external()
		cleartext = memoryview(subprocess.check_output(
					**self.external(),
					input=ciphertext))

		# Verify the header.
		if len(cleartext) < self.external_header_st.size:
			raise SecurityError("Incomplete cleartext header")
		recv_data_type, recv_uuid = \
			self.external_header_st.unpack_from(cleartext)

		if recv_data_type != data_type.value:
			raise SecurityError(
				"Cleartext header mismatch: "
				"data type (0x%.2X) differs from "
				"expected (0x%.2X)"
				% (recv_data_type, data_type.value))

		if self.blob_uuid is None:
			self.blob_uuid = uuid.UUID(bytes=recv_uuid)
		elif recv_uuid != self.blob_uuid.bytes:
			raise SecurityError(
				"Cleartext header mismatch: "
				"snapshot UUID (%s) differs from "
				"expected (%s)"
				% (uuid.UUID(bytes=recv_uuid), self.blob_uuid))

		return cleartext[self.external_header_st.size:]

class MetaBlob(MetaCipher):
	@enum.unique
	class BlobType(enum.IntEnum):
		INDEX	= 0
		FULL	= 1
		DELTA	= 2

	blob: google.cloud.storage.Blob
	blob_type: BlobType
	blob_size: Optional[int]

	subvolume: str
	snapshot_name: str
	snapshot_uuid: uuid.UUID
	parent_uuid: Optional[uuid.UUID]

	def new(self, args: EncryptedBucketOptions,
			blob_uuid: uuid.UUID,
			blob_type: BlobType,
			snapshot: Snapshot,
			parent: Optional[Snapshot]) -> "MetaBlob":
		pass

	def __init__(self, args: EncryptedBucketOptions,
			blob: google.cloud.storage.Blob, blob_name: str):
		super().__init__(args)
		self.blob = blob

		blob_name = blob.name
		if args.prefix is not None:
			prefix = args.prefix + '/'
			assert blob_name.startswith(prefix)
			blob_name = blob_name.removeprefix(prefix)

		signature = None
		if args.encrypt_metadata:
			blob_uuid = blob_name
			try:
				self.blob_uuid = uuid.UUID(blob_uuid)
			except ValueError as ex:
				raise ConsistencyError(
					f"{blob.name} has invalid UUID "
					f"({blob_uuid})") from ex

			blob_type = self.get_integer_metadata(
					self.DataType.BLOB_TYPE, 2)
			try:
				self.blob_type = self.BlobType(blob_type)
			except ValueError as ex:
				raise SecurityError(
					f"{blob.name} has invalid blob_type "
					f"({blob_type})") from ex

			self.snapshot_name = self.get_text_metadata(
					self.DataType.SNAPSHOT_NAME)
		else:
			if self.args.encrypt:
				# Retrieving the metadata should set
				# @self.blob_uuid.  It's safe to use
				# an encrypted hash as a MAC as long as
				# the underlying cipher is non-malleable,
				# which is the case with InternalCipher,
				# being AEAD.
				signature = self.get_binary_metadata(
						self.DataType.SIGNATURE)
				assert self.blob_uuid is not None

			self.snapshot_name, per, blob_type = \
					blob_name.rpartition('/')
			if not per:
				raise ConsistencyError(
					f"{blob.name} is missing blob_type")

			if not blob_type.islower():
				raise ConsistencyError(
					f"{blob.name} has invalid blob_type")
			blob_type = blob_type.upper()
			try:
				self.blob_type = self.BlobType[blob_type]
			except KeyError:
				raise ConsistencyError(
					f"{blob.name} has unknown blob_type "
					f"({blob_type})")

		self.subvolume = self.get_text_metadata(self.DataType.SUBVOLUME)

		self.snapshot_uuid = self.get_uuid_metadata(
						self.DataType.SNAPSHOT_UUID)
		if self.blob_type == self.BlobType.INDEX:
			self.parent_uuid = self.get_uuid_metadata(
						self.DataType.PARENT_UUID)
		elif self.has_metadata(self.DataType.PARENT_UUID):
			raise ConsistencyError(
				"%s[%s]: unexpected metadata"
				% (blob.name,
					self.DataType.PARENT_UUID.field()))
		else:
			self.parent_uuid = None

		if args.verify_blob_size or self.has_metadata(
						self.DataType.BLOB_SIZE):
			self.blob_size = self.get_integer_metadata(
						self.DataType.BLOB_SIZE)
			if blob.size != self.blob_size:
				raise SecurityError(
					"%s has unexpected size (%d != %d)"
					% (blob.name, blob.size,
						self.blob_size))
		else:
			self.blob_size = None

		if signature is not None:
			if signature != self.calc_signature():
				raise SecurityError(
					f"{blob.name} has invalid signature")
		elif self.has_metadata(self.DataType.SIGNATURE):
			raise ConsistencyError(
				"%s[%s]: unexpected metadata"
				% (blob.name, self.DataType.SIGNATURE.field()))

	def calc_signature(self) -> bytes:
		import hashlib

		hasher = hashlib.sha256()
		hasher.update(self.args.subvolume.encode())
		hasher.update(b'\0')
		hasher.update(self.blob_type.value.to_bytes(2, "big"))
		if self.blob_size is not None:
			hasher.update(self.blob_size.to_bytes(8, "big"))
		else:
			hasher.update((-1).to_bytes(8, "big"))
		hasher.update(self.snapshot_name.encode())
		hasher.update(b'\0')
		hasher.update(self.snapshot_uuid.bytes)
		hasher.update(ensure_uuid(self.parent_uuid).bytes)
		return hasher.digest()

	def has_metadata(self, data_type: MetaCipher.DataType) -> bool:
		return self.blob.metadata \
			and data_type.field() in self.blob.metadata

	def get_metadata(self, data_type: MetaCipher.DataType) -> str:
		# TypeError is raised if self.blob.metadata is None.
		try:
			return self.blob.metadata[data_type.field()]
		except (TypeError, KeyError):
			raise SecurityError(
				"%s[%s]: missing metadata"
				% (self.blob.name, data_type.field()))

	def decode_metadata(self, data_type: MetaCipher.DataType,
				metadata: str) -> bytes:
		try:
			return base64.b64decode(metadata, validate=True)
		except binascii.Error as ex:
			raise SecurityError(
				"%s[%s]: couldn't decode metadata"
				% (self.blob.name, data_type.field())) from ex

	def decrypt_metadata(self, data_type: MetaCipher.DataType,
				metadata: str) -> bytes:
		ciphertext = self.decode_metadata(data_type, metadata)
		try:
			return self.decrypt(data_type, ciphertext)
		except FatalError as ex:
			raise ex.__class__(
				"%s[%s]:" % (self.blob.name,
						data_type.field()),
				*ex.args) from ex

	def get_binary_metadata(self, data_type: MetaCipher.DataType) -> bytes:
		metadata = self.get_metadata(data_type)
		if not self.args.encrypt_metadata:
			return self.decode_metadata(data_type, metadata)
		else:
			return self.decrypt_metadata(data_type, metadata)

	def get_text_metadata(self, data_type: MetaCipher.DataType) -> str:
		metadata = self.get_metadata(data_type)
		if not self.args.encrypt_metadata:
			return metadata

		metadata = self.decrypt_metadata(data_type, metadata)
		try:
			return metadata.decode()
		except ValueError as ex:
			raise SecurityError(
				"%s[%s]: invalid metadata"
				% (self.blob.name, data_type.field())) from ex

	def get_integer_metadata(self, data_type: MetaCipher.DataType,
					width: int = 8) -> int:
		metadata = self.get_metadata(data_type)

		if not self.args.encrypt_metadata:
			try:
				return int(metadata)
			except ValueError as ex:
				raise SecurityError(
					"%s[%s]: invalid metadata"
					% (self.blob.name,
						data_type.field())) from ex

		metadata = self.decrypt_metadata(data_type, metadata)
		if len(metadata) != width:
			raise SecurityError(
				"%s[%s]: unexpected metadata size (%d != %d)"
				% (self.blob.name, data_type.field(),
					len(metadata), width))
		return int.from_bytes(metadata, "big")

	def get_uuid_metadata(self, data_type: MetaCipher.DataType) \
				-> uuid.UUID:
		metadata = self.get_metadata(data_type)

		if not self.args.encrypt_metadata:
			try:
				return uuid.UUID(metadata)
			except ValueError as ex:
				raise SecurityError(
					"%s[%s]: invalid metadata"
					% (self.blob.name,
						data_type.field())) from ex

		metadata = self.decrypt_metadata(data_type, metadata)
		try:
			return uuid.UUID(bytes=metadata)
		except ValueError as ex:
			raise SecurityError(
				"%s[%s]: invalid metadata"
				% (self.blob.name, data_type.field())) \
				from ex

	def set_metadata(self,
			blob: google.cloud.storage.Blob,
			data_type: MetaCipher.DataType, data: bytes) -> None:
		if self.args.encrypt:
			data = self.encrypt(data_type, data)

		if blob.metadata is None:
			blob.metadata = { }
		blob.metadata[data_type.field()] = \
			base64.b64encode(data).decode()

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

		if self.interval is not None:
			print(" %s (%s)" % (
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
	StdioType = Union[None, int, io.IOBase]

	_stdin: StdioType
	_stdout: StdioType

	def __init__(self,
			cmds: Sequence[Union[Sequence[str], dict[str, Any]]],
			stdin: StdioType = subprocess.DEVNULL,
			stdout: StdioType = None):
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

		self._stdin = stdin
		self._stdout = stdout
		if not self.processes \
				and stdin == subprocess.PIPE \
				and stdout == subprocess.PIPE:
			# This is deadlock-prone.
			stdin, stdout = os.pipe()
			self._stdin = open(stdin, "rb")
			self._stdout = open(stdout, "wb")

	def __del__(self):
		for proc in self.processes:
			try:
				proc.kill()
				proc.wait()
			except:
				pass

	def __len__(self) -> int:
		return len(self.processes)

	def __getitem__(self, i: int) -> subprocess.Popen:
		return self.processes[i]

	# Return a file that can be written to.
	def stdin(self) -> Optional[BinaryIO]:
		if self.processes:
			return self.processes[0].stdin
		elif self._stdout is subprocess.DEVNULL:
			return open(os.devnull, "wb")
		else:
			assert isinstance(self._stdout,
						(type(None), io.IOBase))
			return self._stdout

	# Return a file that can be read from.
	def stdout(self) -> Optional[BinaryIO]:
		if self.processes:
			return self.processes[-1].stdout
		elif self._stdin is subprocess.DEVNULL:
			return open(os.devnull, "b")
		else:
			assert isinstance(self._stdin,
						(type(None), io.IOBase))
			return self._stdin

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
# Remove all values from a dict which don't match the predicate.
def filter_dict(d: dict[Any, Any], keep: Callable[[Any], bool]) -> None:
	to_cull = [ key for key, val in d.items() if not keep(val) ]
	for key in to_cull:
		del d[key]

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

def woulda(args: DryRunOptions, verb: str) -> str:
	return f"Would have {verb}" if args.is_dry_run() else verb.capitalize()
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
def delete_snapshot(args: DryRunOptions, fs: OpenDir, snapshot: Snapshot) \
			-> None:
	if args.is_dry_run():
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
			-> dict[uuid.UUID, Snapshot]:
	return { snapshot.uuid: snapshot for snapshot in snapshots }
# }}}

# Backup-related functions {{{
# Go through the blobs of a GCS bucket and create Backup:s from them.
def discover_remote_backups(args: EncryptedBucketOptions,
				keep_index_only: bool = False) \
				-> dict[uuid.UUID, Backup]:
	prefix = args.prefix
	if prefix is not None:
		prefix += '/'

	by_uuid = { }
	by_fname = { }
	for blob in args.find_bucket().list_blobs(prefix=prefix):
		fname, per, suffix = blob.name.rpartition('/')
		if not per:
			raise ConsistencyError(
					f"Invalid blob name {blob.name}")

		if suffix == "" and blob.size == 0:
			# Placeholder file for a directory.
			continue

		if not suffix.islower():
			raise ConsistencyError(
					f"{blob.name} has invalid suffix")
		suffix = suffix.upper()
		if suffix not in BlobType.__members__:
			raise ConsistencyError(
					f"{blob.name} has unknown suffix")
		blob_type = BlobType[suffix]

		if prefix is not None:
			if not fname.startswith(prefix):
				raise ConsistencyError(
					"%s's prefix is not %s"
					% (blob.name, prefix))
			fname = fname.removeprefix(prefix)
		elif '/' in fname:
			# Ignore blobs that could have a prefix.
			continue

		if "uuid" not in blob.metadata:
			raise ConsistencyError(f"{blob.name} has no UUID")
		try:
			blob_uuid = uuid.UUID(blob.metadata["uuid"])
		except ValueError as ex:
			raise ConsistencyError(
				f"{blob.name} has invalid UUID") from ex

		try:
			existing = by_fname[fname]
		except KeyError:
			existing = by_uuid.get(blob_uuid)
			if existing is not None:
				raise ConsistencyError(
					"%s and %s have the same UUID"
					% (blob.name,
						existing.any_blob().name))

			backup = Backup(fname, blob_uuid)
			backup.set_blob(blob_type, blob)
			by_uuid[blob_uuid] = by_fname[fname] = backup
		else:	# There's an @existing Backup.
			if blob_uuid != existing.uuid:
				raise ConsistencyError(
					"%s and %s have different UUIDs"
					% (blob.name,
						existing.any_blob().name))
			existing.set_blob(blob_type, blob)

	if keep_index_only:
		# Keep only Backup:s with an index.
		predicate = lambda backup: backup.index is not None
	else:	# Delete orphan Backup:s.
		predicate = lambda backup: not backup.orphan()
	filter_dict(by_uuid, predicate)

	return by_uuid

# Is the Backup identified by its UUID a full backup or is it restorable
# from its parent Backup:s?
def backup_restorable(snapshot_uuid: Optional[uuid.UUID],
			remote_backups: dict[uuid.UUID, Backup]) -> bool:
	if snapshot_uuid is None:
		return False
	backup = remote_backups.get(snapshot_uuid)
	if backup is None:
		return False

	if backup.restorable is None:
		if backup.full is not None:
			backup.restorable = True
		else:	# @backup only has a delta, determine if its parent
			# is restorable, then cache the result.
			backup.restorable = backup_restorable(
						backup.parent, remote_backups)
	return backup.restorable
# }}}

# Snapshot selection {{{
# Return the index of a Snapshot in a sequence of Snapshot:s.
def find_snapshot(snapshots: Sequence[Snapshot],
			snapshots_by_uuid: dict[uuid.UUID, Snapshot],
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
def choose_exact_snapshots(args: SelectionOptions, where: str,
				snapshots: Sequence[Snapshot],
				indexes: list[int]) -> bool:
	if not args.exact:
		return False
	assert not args.first and args.frm is None and args.to is None

	# Return the @indexes of @exacts in @snapshots.
	exacts = set(args.exact)
	for i, snapshot in enumerate(snapshots):
		try:
			if args.use_uuid:
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
		errors = [ "The following items were not found %s:"
				% where ]
		errors += ("  %s" % exact for exact in exacts)
		raise UserError("\n".join(errors))

	return True

# Return the index of the first and last snapshots selected by
# --first/--from/--to.
def choose_snapshot_range(args: SelectionOptions, where: str,
				snapshots: Sequence[Snapshot],
				snapshots_by_uuid: dict[uuid.UUID, Snapshot]) \
				-> tuple[Optional[int], Optional[int]]:
	assert not args.exact

	# Determine the @first and @last snapshots in the range.
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
def choose_snapshots(args: SelectionOptions, where: str,
			snapshots: Sequence[Snapshot],
			snapshots_by_uuid: dict[uuid.UUID, Snapshot]) \
			-> Collection[int]:
	exacts = [ ]
	if choose_exact_snapshots(args, where, snapshots, exacts):
		return exacts

	first, last = choose_snapshot_range(args, where,
						snapshots, snapshots_by_uuid)
	if first is not None:
		assert last is not None
		return range(first, last+1)
	elif last is not None:
		return range(last+1)
	else:	# @first and @last are None.
		return ()
# }}}

# Encryption functions {{{
CipherClass = TypeVar("CipherClass", bound=InternalCipher)
def get_cipher(args: EncryptionOptions, cipher_class: CipherClass,
		blob: google.cloud.storage.Blob,
		blob_type: BlobType, blob_uuid: uuid.UUID) \
		-> Union[None, dict[str, Any], CipherClass]:
	if not args.encrypt:
		return None

	# Add environment variables that allow the external programs to retrieve
	# blob-specific keys.
	env = os.environ.copy()
	env["GICCS_SUBVOLUME"] = args.subvolume
	env["GICCS_BLOB_UUID"] = str(blob_uuid)

	if args.cipher_command is not None:
		return { "args": args.cipher_command, "env": env }

	if args.encryption_key is not None:
		key = args.encryption_key
	else:
		assert args.encryption_key_command is not None
		key = subprocess.check_output(args.encryption_key_command, env=env)

	return cipher_class(key,
		blob_type.data_type_id(EncryptedDataType.PAYLOAD),
			blob_uuid)

def encrypt_metadata(args: EncryptionOptions,
			cipher: Union[InternalEncrypt, dict[str, Any]],
			data_type_id: int, blob_uuid: uuid.UUID,
			cleartext: bytes) -> str:
	if isinstance(cipher, InternalCipher):
		ciphertext = InternalEncrypt(cipher.key,
				data_type_id, blob_uuid,
				wrapped=io.BytesIO(cleartext)).read()
	else:	# Metadata always have a header.
		header = encryption_header_st.pack(
				data_type_id, blob_uuid.bytes)
		ciphertext = subprocess.check_output(**cipher,
				input=header + cleartext)

	return base64.b64encode(ciphertext).decode()

def decrypt_metadata(args: EncryptionOptions,
			cipher: Union[InternalDecrypt, dict[str, Any]],
			data_type_id: int, blob_uuid: Optional[uuid.UUID],
			ciphertext: bytes) -> memoryview:
	# Decoding errors are handled by the caller.
	ciphertext = base64.b64decode(ciphertext, validate=True)
	if isinstance(cipher, InternalCipher):
		cleartext = io.BytesIO()
		cipher = InternalDecrypt(cipher.key,
						data_type_id, blob_uuid,
						cleartext)
		cipher.write(ciphertext)
		cipher.close()
		return cleartext.getbuffer()

	# @cipher is non-InternalCipher.
	cleartext = memoryview(subprocess.check_output(
				**cipher, input=ciphertext))

	# Verify the header.
	if len(cleartext) < encryption_header_st.size:
		raise SecurityError("Incomplete metadata header")
	recv_data_type_id, recv_uuid = \
		encryption_header_st.unpack_from(cleartext)

	if recv_data_type_id != data_type_id:
		raise SecurityError(
			"Metadata header mismatch: "
			"data type ID (%.2X) differs from expected (%.2X)"
			% (recv_data_type_id, data_type_id))

	blob_uuid = ensure_uuid(blob_uuid)
	if recv_uuid != blob_uuid.bytes:
		raise SecurityError(
			"Metadata header mismatch: "
			"snapshot UUID (%s) differs from expected (%s)"
			% (uuid.UUID(bytes=recv_uuid), blob_uuid))

	return cleartext[encryption_header_st.size:]
# }}}

# Blob-related functions {{{
def make_blob(bucket: google.cloud.storage.Bucket,
		prefix: Optional[str], snapshot: Snapshot, suffix: str,
		metadata: dict[str, str] = { }) \
		-> google.cloud.storage.Blob:
	blob_name = f"{snapshot.fname}/{suffix}"
	if prefix is not None:
		blob_name = f"{prefix}/{blob_name}"
	blob = bucket.blob(blob_name)

	metadata["uuid"] = str(snapshot.uuid)
	blob.metadata = metadata

	return blob

# Write @blob_type and @blob_uuid as binary to @sys.stdout.
def write_header(blob_type: BlobType, blob_uuid: uuid.UUID) \
		-> Callable[[], None]:
	def write_header():
		# Redirect this function's stdout to stderr, so it doesn't
		# go into the pipeline by accident.
		stdout, sys.stdout = sys.stdout, sys.stderr

		try:
			os.write(stdout.fileno(),
				encryption_header_st.pack(
					blob_type.data_type_id(
						EncryptedDataType.PAYLOAD),
					blob_uuid.bytes))
		except Exception as ex:
			# The contents of exceptions are not passed back
			# to the main interpreter, so let's print it here.
			print(ex, file=sys.stderr)
			raise

	return write_header

def upload_blob(args: UploadBlobOptions,
		blob: google.cloud.storage.Blob,
		blob_type: BlobType, blob_uuid: uuid.UUID,
		command: Sequence[str]) -> int:
	cipher = get_cipher(args, InternalEncrypt, blob,
				blob_type, blob_uuid)
	if cipher is not None and not isinstance(cipher, InternalEncrypt) \
			and args.add_header_to_blob:
		# Write @blob_type and @blob_uuid into the pipeline
		# before the @command is executed.  We rely on the pipe
		# having capacity for ~16 bytes, otherwise there will be
		# a deadlock.
		#
		# If we're using InternalEncrypt, it will add the headers
		# itself.
		command = {
			"args": command,
			"preexec_fn": write_header(blob_type, blob_uuid),
		}

	pipeline = [ command ]
	if args.compressor is not None:
		pipeline.append(args.compressor)
	if isinstance(cipher, dict):
		pipeline.append(cipher)
	pipeline = Pipeline(pipeline, stdout=subprocess.PIPE)

	if isinstance(cipher, InternalCipher):
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
			flags = args.get_retry_flags()
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
			if args.reupload:
				raise ConsistencyError(
					"%s does not exist in bucket"
					% blob.name)
			else:
				raise ConsistencyError(
					"%s already exists in bucket"
					% blob.name)
		except GoogleAPICallError as ex:
			raise FatalError(ex) from ex
	else:	# In case of --wet-run just read @src until we hit EOF.
		if not args.ignore_remote:
			exists = blob.bucket.get_blob(blob.name) != None
			if exists and not args.reupload:
				raise ConsistencyError(
					"%s already exists in bucket"
					% blob.name)
			elif args.reupload and not exists:
				raise ConsistencyError(
					"%s does not exist in bucket"
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
		size = encrypt_metadata(
				args, cipher,
				blob_type.data_type_id(EncryptedDataType.SIZE),
				blob_uuid,
				src.bytes_transferred.to_bytes(8, "big"))
		blob.metadata = { "expected_size":  size }
		if not args.wet_run:
			# If case of failure the blob won't be usable without
			# --no-verify-blob-size, so it's okay not to delete it.
			blob.patch()

	return src.bytes_transferred

# Read a pair of UUIDs from stdin and compare them to the expected ones
# passed through sys.argv.  If they check out, execute sys.argv[4].
HEADER_VERIFICATION_SCRIPT = """
import sys, os
import struct, uuid

# Set a more informative COMM than "python3" for wait_proc().
try:
	fd = os.open("/proc/self/comm", os.O_WRONLY)
except FileNotFoundError:
	pass
else:
	os.write(fd, b"verify_header")
	os.close(fd)

# sys.argv[0] is "-c".
expected_data_type_id = int(sys.argv[1])
expected_uuid = uuid.UUID(sys.argv[2])

# Read and parse the @header.
encryption_header_st = struct.Struct("{encryption_header_st}")
header = os.read(sys.stdin.fileno(), encryption_header_st.size)
if len(header) < encryption_header_st.size:
	sys.exit("Failed to read encryption header, only got %d bytes."
			% len(header))
recv_data_type_id, recv_uuid = encryption_header_st.unpack_from(header)

# Verify the @header.
if recv_data_type_id != expected_data_type_id:
	sys.exit("Data type ID (0x%.2X) differs from expected (0x%.2X)."
			% (recv_data_type_id, expected_data_type_id))

if recv_uuid != expected_uuid.bytes:
	sys.exit("Snapshot UUID (%s) differs from expected (%s)."
			% (uuid.UUID(bytes=recv_uuid), expected_uuid))

# Execute btrfs receive.
os.execvp(sys.argv[3], sys.argv[3:])
""".format(encryption_header_st=encryption_header_st.format)

def download_blob(args: DownloadBlobOptions,
		blob: google.cloud.storage.Blob,
		blob_type: BlobType, blob_uuid: uuid.UUID,
		command: Union[None, Sequence[str], dict[str, Any]] = None,
		pipeline_stdout: Pipeline.StdioType = None,
		pipeline_callback:
			Optional[Callable[[Pipeline], None]] = None) -> int:
	cipher = get_cipher(args, InternalDecrypt, blob,
				blob_type, blob_uuid)
	if cipher is not None and args.verify_blob_size:
		if "expected_size" not in blob.metadata:
			raise SecurityError(
				"%s is missing expected_size metadata"
				% blob.name)
		try:
			expected_size = decrypt_metadata(
				args, cipher,
				blob_type.data_type_id(EncryptedDataType.SIZE),
				blob_uuid,
				blob.metadata["expected_size"])
		except binascii.Error as ex:
			raise SecurityError(
				f"{blob.name}[expected_size]: "
				"couldn't decode metadata")
		except FatalError as ex:
			raise ex.__class__(
				f"{blob.name}[expected_size]:", *ex.args) \
				from ex
		else:
			expected_size = int.from_bytes(expected_size, "big")
		if blob.size != expected_size:
			raise SecurityError(
					"%s has unexpected size (%d != %d)"
					% (blob.name, blob.size,
						expected_size))

	if cipher is not None and not isinstance(cipher, InternalDecrypt) \
			and args.add_header_to_blob:
		# Wrap @command with the @HEADER_VERIFICATION_SCRIPT,
		# and pass it the expected UUIDs.
		if command is None:
			command_args = ("cat",)
		elif isinstance(command, dict):
			command_args = command["args"]
		else:
			command_args = command

		if not isinstance(command, dict):
			command = { }
		command["args"] = \
			("python3", "-c", HEADER_VERIFICATION_SCRIPT,
				str(blob_type.data_type_id(
					EncryptedDataType.PAYLOAD)),
				str(blob_uuid)) \
			+ command_args
		command["executable"] = sys.executable

	pipeline = [ ]
	if isinstance(cipher, dict):
		pipeline.append(cipher)
	if args.compressor is not None:
		pipeline.append(args.compressor)
	if command is not None:
		pipeline.append(command)

	# @pipeline could be empty.
	pipeline = Pipeline(pipeline,
				stdin=subprocess.PIPE,
				stdout=pipeline_stdout)
	if isinstance(cipher, InternalCipher):
		cipher.init(pipeline.stdin())
		dst = cipher
	else:
		dst = pipeline.stdin()
	dst = Progressometer(dst, args.progress, blob.size)

	try:	# The actual download.
		blob.download_to_file(dst, **args.get_retry_flags())
		dst.final_progress()
		if isinstance(cipher, InternalDecrypt):
			cipher.close()
	except (Exception, KeyboardInterrupt) as ex:
		if isinstance(ex, GoogleAPICallError):
			raise FatalError(ex) from ex
		raise
	finally:
		if len(pipeline) > 0:
			# This should cause the @pipeline to finish.
			pipeline.stdin().close()
		if pipeline_callback is not None:
			# And this one should consume the @pipeline's
			# stdout or stderr.
			pipeline_callback(pipeline)

	# It should be safe to wait for the @pipeline now that it has been read.
	# If it wasn't, we could deadlock.
	pipeline.wait()

	# If there's a mismatch Progressometer.final_progress() should have
	# caught it.
	assert dst.bytes_transferred == blob.size
	return dst.bytes_transferred
# }}}

# The list buckets subcommand {{{
class CmdListBuckets(CmdLeaf, CommonOptions):
	cmd = "buckets"
	help = "TODO"

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.add_dir()

	def execute(self) -> None:
		cmd_list_buckets(self)

def cmd_list_buckets(args: CmdListBuckets) -> None:
	found = False
	for bucket in args.get_gcs_client().list_buckets():
		if not args.bucket_matches(bucket):
			continue
		found = True

		labels = ", ".join(
			key if not val else "%s=%s" % (key, repr(val))
			for key, val in bucket.labels.items())
		if labels:
			print(bucket.name, labels)
		else:
			print(bucket.name)

	if not found:
		raise UserError("Bucket not found")
# }}}

 # The list local subcommand {{{
class CmdListLocal(CmdLeaf, CommonOptions, ShowUUIDOptions):
	cmd = "local"
	help = "TODO"

	check_remote: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["other"]
		section.add_enable_flag("--check-remote", "-r")

		self.add_dir()

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.check_remote = args.check_remote
		if self.check_remote:
			self.bucket_required = True

	def execute(self) -> None:
		cmd_list_local(self)

def cmd_list_local(args: CmdListLocal) -> None:
	remote_backups = discover_remote_backups(args) \
				if args.check_remote else None

	for snapshot in sorted(discover_local_snapshots(args.dir)):
		if remote_backups is None:
			print(snapshot)
		elif snapshot.uuid in remote_backups:
			print("%s: present remotely" % snapshot)
		else:
			print("%s: absent remotely" % snapshot)
# }}}

 # The list remote subcommand {{{
class CmdListRemote(CmdLeaf, ListRemoteOptions):
	cmd = "remote"
	help = "TODO"

	def declare_arguments(self) -> None:
		super().declare_arguments()

		# We need to differentiate whether the directory is specified
		# or not.
		self.add_dir(default=False)

	def execute(self) -> None:
		cmd_list_remote(self)

def cmd_list_remote(args: CmdListRemote) -> None:
	local_snapshots = \
		uuid_to_snapshots(discover_local_snapshots(args.dir)) \
		if args.dir is not None else None
	remote_backups = discover_remote_backups(args)

	nbytes = 0
	nbackups = 0
	for backup in sorted(remote_backups.values()):
		if local_snapshots is None:
			print(backup)
		elif backup.uuid in local_snapshots:
			print(f"{backup}: present locally")
		else:
			print(f"{backup}: absent locally")

		for which in ("index", "full", "delta"):
			blob = getattr(backup, which)
			if blob is None:
				continue

			if which in ("full", "delta"):
				nbackups += 1
				nbytes += blob.size

			if args.verbose:
				created = blob.time_created.timestamp()
				print("", which,
					time.strftime("%Y-%m-%d %H:%M:%S",
						time.localtime(created)),
					humanize_size(blob.size),
					sep="\t")

	if args.verbose and nbackups > 1:
		print()
		print("%d backups in %s." % (nbackups, humanize_size(nbytes)))
# }}}

# The delete local subcommand {{{
class CmdDeleteLocal(CmdLeaf, DeleteOptions, SnapshotSelectionOptions):
	cmd = "local"
	help = "TODO"

	selection_section = "snapshot"

	force:		bool = False
	force_all:	bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["force"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag("--force")
		mutex.add_enable_flag("--force-all")

		self.add_dir()

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.force = args.force
		self.force_all = args.force_all
		if not self.force_all:
			# We're not blindly deleting everything selected,
			# so we need a bucket for checking what is available
			# remotely.
			self.bucket_required = True

	def execute(self) -> None:
		cmd_delete_local(self)

def snapshot_restorable(snapshot: Snapshot,
			remote_backups: dict[uuid.UUID, Backup]) -> bool:
	return backup_restorable(snapshot.uuid, remote_backups)

def cmd_delete_local(args: CmdDeleteLocal) -> None:
	local_by_uuid = uuid_to_snapshots(discover_local_snapshots(args.dir))
	local_snapshots = sorted(local_by_uuid.values())

	# We don't need to consider the @remote_backups if --force-all.
	if not args.force_all:
		remote_backups = discover_remote_backups(args)

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
# }}}

# The delete remote subcommand {{{
class CmdDeleteRemote(CmdLeaf, DeleteOptions):
	cmd = "remote"
	help = "TODO"

	bucket_required = True
	selection_section = "backup"

	prefer_full:		bool = False
	delete_full:		bool = False
	prefer_delta:		bool = False
	delete_delta:		bool = False
	delete_delta_broken:	bool = False

	force:			bool = False
	force_all:		bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["rmdelete"]
		mutex = section.add_mutually_exclusive_group(required=True)
		mutex.add_enable_flag("--delete-full")
		mutex.add_enable_flag("--delete-delta")
		mutex.add_enable_flag("--delete-delta-broken")
		mutex.add_enable_flag("--delete-full-delta")
		mutex.add_enable_flag("--delete-delta-full")

		section = self.sections["force"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag("--force")
		mutex.add_enable_flag("--force-all")

		self.add_dir()

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.force = args.force
		self.force_all = args.force_all
		force = self.force or self.force_all

		if args.delete_delta_broken and force:
			raise self.CmdLineError(
				"--force/--force-all doesn't make sense "
				"with --delete-delta-broken")
		elif args.delete_delta_full and not force:
			raise self.CmdLineError(
				"--delete-delta-full doesn't make sense "
				"without --force or --force-all")
		elif args.delete_full_delta and not force:
			# This is like --delete-full --delete-delta-broken.
			pass

		self.delete_full = args.delete_full \
			or args.delete_full_delta or args.delete_delta_full
		self.delete_delta = args.delete_delta \
			or args.delete_full_delta or args.delete_delta_full
		self.prefer_full = args.delete_full or args.delete_full_delta
		self.prefer_delta = args.delete_delta or args.delete_delta_full
		self.delete_delta_broken = args.delete_delta_broken

	def execute(self) -> None:
		cmd_delete_remote(self)

def cmd_delete_remote(args: CmdDeleteRemote) -> None:
	# Only take @local_snapshots into account if --force:d.
	local_snapshots = \
		uuid_to_snapshots(discover_local_snapshots(args.dir)) \
		if args.force else { }

	remote_by_uuid = discover_remote_backups(args)
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

	# Delete snapshots.
	ndeleted = 0
	deleted_bytes = 0
	for i in to_delete:
		backup = remote_backups[i]

		# In other words: {{{
		#
		# Delete @backup.full?
		# 	if --delete-full or --delete-full-delta:
		# 		if force and present locally:
		# 			delete @backup.full (present)
		# 		elif restorable from backup.delta:
		# 			delete @backup.full (restorable)
		# 	elif --delete-delta:
		# 		don't delete @backup.full
		# 	elif --delete-delta-full:
		# 		if force and present locally:
		# 			delete @backup.full (present)
		#
		# Delete @backup.delta?
		# 	if --delete-delta or --delete-delta-full:
		# 		if force and present locally:
		# 			delete @backup.delta (present)
		# 		elif backup.full exists:
		# 			delete @backup.delta (full)
		# 		elif not restorable from @backup.delta:
		# 			delete @backup.delta (broken)
		# 	elif --delete-full:
		# 		don't delete @backup.delta
		# 	elif --delete-full-delta:
		# 		if force and present locally:
		# 			delete @backup.delta (present)
		# 		elif not restorable from @backup.delta:
		# 			delete @backup.delta (broken)
		# }}}
		which_to_delete: list[tuple[BlobType, str]] = [ ]
		if args.force_all or backup.uuid in local_snapshots:
			# --force or --force-all
			reason = "snapshot is present locally" \
				if not args.force_all else None
			if args.delete_full:
				which_to_delete.append(
					(BlobType.FULL, reason))
			if args.delete_delta:
				which_to_delete.append(
					(BlobType.DELTA, reason))
		elif args.prefer_delta and backup.full is not None:
			which_to_delete.append((
					BlobType.DELTA,
					"full backup is available"))
		elif backup_restorable(backup.parent, remote_by_uuid):
			if args.prefer_full:
				which_to_delete.append((
					BlobType.FULL,
					"backup is restorable incrementally"))
		else:	# Not restorable from delta.
			if args.delete_delta or args.delete_delta_broken:
				which_to_delete.append((
					BlobType.DELTA,
					"incremental backup chain is broken"))

		prev_ndeleted = ndeleted
		for which, reason in which_to_delete:
			blob = backup.blobs[which]
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
			backup.clear_blob(which)

		# Delete @backup.index if we've deleted all backups.
		if ndeleted > prev_ndeleted and backup.index is not None \
				and backup.orphan():
			blob = backup.index
			deleted_bytes += blob.size

			print("Deleting %s..." % blob.name)
			blob.delete()

	if ndeleted > 0:
		print()
		print("%s %d backups(s) (%s)."
			% (woulda(args, "deleted"), ndeleted,
				humanize_size(deleted_bytes)))
	else:
		print("Would not have deleted anything.")
# }}}

# The upload subcommand {{{
class CmdUpload(CmdLeaf, UploadDownloadOptions, UploadBlobOptions,
		SnapshotSelectionOptions):
	cmd = "upload"
	help = "TODO"

	selection_section = "snapshot"

	index: Optional[bool] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["index"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag_no_dflt("--index")
		mutex.add_disable_flag_no_dflt("--no-index")
		section.add_argument("--indexer")
		section.add_argument("--index-fmt")

		self.add_dir()

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args, "indexer")
		if args.indexer is not None:
			self.indexer = self.shlex_split(
						"indexer", args.indexer)
		else:
			self.indexer = (
				"find", "{snapshot_dir}",
				"-mindepth", "1",
				"(",
					"-type", "l",
					"-printf", r"{index_fmt}\t%P -> %l\n",
				")", "-o",
				"-printf", r"{index_fmt}\t%P\n",
			)

		self.merge_options_from_ini(args, "index_fmt")
		if args.index_fmt is not None:
			self.index_fmt = args.index_fmt
		else:
			self.index_fmt = r"%y %TY-%Tm-%Td %TH:%TM:%TS %s"

		self.merge_options_from_ini(args, "index", tpe=bool)
		if args.index is not None:
			self.index = args.index
		elif args.indexer is not None or args.index_fmt is not None:
			self.index = True

	def execute(self) -> None:
		cmd_upload(self)

def upload_index(args: CmdUpload, snapshot: Snapshot) -> int:
	if args.dry_run:
		print(f"Would upload {snapshot}'s index.")
		return 0

	print(f"Uploading {snapshot}'s index...", end="", flush=True)
	try:
		# Substitute {snapshot_dir} and {index_fmt} in args.indexer.
		snapshot_dir = os.path.join(args.dir, snapshot.fname)
		def transformer(arg: str) -> str:
			return arg.format(
				snapshot_dir=snapshot_dir,
				index_fmt=args.index_fmt)

		with args.override_flags(
				compressor=args.index_compressor,
				encrypt=args.encrypt_index):
			return upload_blob(args,
				make_blob(args.bucket, args.prefix,
						snapshot, "index"),
				BlobType.INDEX, snapshot.uuid,
				tuple(map(transformer, args.indexer)))
	finally:
		print()

def upload_snapshot(
		args: CmdUpload,
		blob: google.cloud.storage.Blob,
		blob_type: BlobType, blob_uuid: uuid.UUID,
		btrfs_send: Sequence[str]) -> int:
	if args.wet_run_no_data:
		btrfs_send = (*btrfs_send, "--no-data")
	return upload_blob(args, blob, blob_type, blob_uuid, btrfs_send)

def upload_full(args: CmdUpload, snapshot: Snapshot) -> int:
	if args.dry_run:
		print(f"Would upload {snapshot} in full.")
		return 0

	print(f"Uploading {snapshot} in full...", end="", flush=True)
	try:
		return upload_snapshot(args,
			make_blob(args.bucket, args.prefix, snapshot, "full"),
			BlobType.FULL, snapshot.uuid,
			("btrfs", "-q", "send",
				os.path.join(args.dir, snapshot.fname)))
	finally:
		print()

def upload_delta(args: CmdUpload, snapshot: Snapshot, parent: Snapshot) -> int:
	if args.dry_run:
		print(f"Would upload {snapshot} delta from {parent}.")
		return 0

	print(f"Uploading {snapshot} delta from {parent}...",
		end="", flush=True)
	try:
		return upload_snapshot(args,
			make_blob(args.bucket, args.prefix, snapshot, "delta",
					{"parent": str(parent.uuid)}),
			BlobType.DELTA, snapshot.uuid,
			("btrfs", "-q", "send",
				"-p", os.path.join(args.dir, parent.fname),
				os.path.join(args.dir, snapshot.fname)))
	finally:
		print()

def cmd_upload(args: CmdUpload) -> None:
	local_by_uuid = uuid_to_snapshots(discover_local_snapshots(args.dir))
	local_snapshots = sorted(local_by_uuid.values())
	remote_backups = discover_remote_backups(args) \
				if not args.ignore_remote else { }

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
			if backup is not None and backup.parent is not None \
					and backup.parent != parent.uuid:
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
			bytes_transferred += upload_full(args, snapshot)
			snapshots_transferred += 1
		if should_upload_delta:
			assert parent is not None
			bytes_transferred += upload_delta(args, snapshot, parent)
			snapshots_transferred += 1
		if should_upload_full or should_upload_delta:
			remote_backups[snapshot.uuid] = snapshot
		else:
			assert backup is not None
			if not args.reupload:
				print(f"{snapshot} is already backed up.")

		# upload_index()
		if args.reupload:
			assert backup is not None
			should_upload_index = backup.index is not None
			should_upload_index &= args.index is not False
		else:
			should_upload_index = backup is None \
						or backup.index is None
			should_upload_index &= args.index is True
		if should_upload_index:
			bytes_transferred += upload_index(args, snapshot)

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

# The download subcommand {{{
class CmdDownload(CmdLeaf, DownloadBlobOptions, UploadDownloadOptions):
	cmd = "download"
	help = "TODO"

	selection_section = "backup"

	ignore_local: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["operation"]
		section.add_enable_flag("--ignore-local")

		self.add_dir()

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.ignore_local = args.ignore_local
		if self.ignore_local and not (self.dry_run or self.wet_run):
			raise self.CmdLineError(
					"--ignore-local only makes sense "
					"with --dry-run/--wet-run")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		if self.autodelete:
			if self.first or self.frm is not None or self.exact:
				# --first/--from/--exact imply we don't want
				# to delete the selected backups.
				raise self.CmdLineError(
						"cannot specify --autodelete "
						"with --first/--from/--exact")

	def execute(self) -> None:
		cmd_download(self)

def download_backup(
		args: CmdDownload, fname: str,
		blob: google.cloud.storage.Blob,
		blob_type: BlobType, blob_uuid: uuid.UUID,
		btrfs_recv: Sequence[str]) -> int:
	if not args.ignore_local and os.path.exists(
					os.path.join(args.dir, fname)):
		raise UserError(f"{fname} already exists")

	pipeline_stdout = None
	if not args.wet_run:
		# We'll need to parse @btrfs_recv's output.
		btrfs_recv = { "args": btrfs_recv }
		if blob_type == BlobType.FULL:
			# @btrfs_recv prints "At subvol ..." on stderr.
			btrfs_recv["stderr"] = subprocess.PIPE
		else:	# @btrfs_recv prints "At snapshot ..." on stdout.
			pipeline_stdout = subprocess.PIPE
	else:	# --wet-run
		pipeline_stdout = subprocess.DEVNULL
		if not args.wet_run_no_data:
			btrfs_recv = (*btrfs_recv[:-1], "--dump")
		else:
			btrfs_recv = None

	# @btrfs_recv writes the snapshot it creates to its stdout or stderr.
	# This can be different from the intended destination @fname in case
	# the backup was renamed in GCS.
	subvol = None
	def extract_new_subvol(pipeline: Pipeline) -> None:
		if args.wet_run:
			return
		assert len(pipeline) > 0

		# The message is different if we restore from delta or not.
		if blob_type == BlobType.FULL:
			fin = pipeline[-1].stderr
			fout = sys.stderr
			pattern = re.compile("^At subvol (.+)\n")
		else:
			fin = pipeline[-1].stdout
			fout = sys.stdout
			pattern = re.compile("^At snapshot (.+)\n")

		# Parse @fin with @pattern.
		out = io.TextIOWrapper(fin).read()
		match = pattern.match(out)
		if match:
			nonlocal subvol
			subvol = match.group(1)

			# Remove @pattern from @out.
			out = pattern.sub("", out)

		if out:	# Print @out as if it was output by @btrfs_recv.
			# Make it more visible by adding a newline.
			print()
			fout.write(out)

	try:
		return download_blob(args,
			blob, blob_type, blob_uuid,
			btrfs_recv, pipeline_stdout,
			extract_new_subvol)
	except:
		if subvol is not None:
			# Don't leave behind a potentially corrupted snapshot.
			delete_subvol(OpenDir(args.dir), subvol)
		raise
	else:
		if subvol is not None and subvol != fname:
			os.rename(os.path.join(args.dir, subvol),
					os.path.join(args.dir, fname))

def download_full(args: CmdDownload, backup: Backup) -> int:
	size = humanize_size(backup.full.size)
	if args.dry_run:
		print(f"Would download {backup} in full ({size}).")
		return backup.full.size

	print(f"Downloading {backup} in full ({size})...", end="", flush=True)
	try:
		return download_backup(args,
			backup.fname, backup.full,
			BlobType.FULL, backup.uuid,
			("btrfs", "receive", args.dir))
	finally:
		print()

def download_delta(args: CmdDownload, backup: Backup,
			parent: Snapshot) -> int:
	size = humanize_size(backup.delta.size)
	if args.dry_run:
		print(f"Would download {backup} delta from {parent} ({size}).")
		return backup.delta.size

	print(f"Downloading {backup} delta from {parent} ({size})...",
		end="", flush=True)
	try:
		return download_backup(args,
			backup.fname, backup.delta,
			BlobType.DELTA, backup.uuid,
			("btrfs", "receive", args.dir))
	finally:
		print()

def cmd_download(args: CmdDownload) -> None:
	local_snapshots = \
		uuid_to_snapshots(discover_local_snapshots(args.dir)) \
		if not args.ignore_local else { }

	remote_by_uuid = discover_remote_backups(args)
	remote_backups = sorted(remote_by_uuid.values())

	# Validate the parent-child relationships in @remote_backups.
	for i, backup in enumerate(remote_backups):
		if backup.parent is None:
			continue
		parent = remote_by_uuid.get(backup.parent)
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
				backup = remote_by_uuid.get(backup.parent)

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

		if backup.parent is not None:
			parent = local_snapshots.get(backup.parent)
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
					f"{backup.parent} "
					f"(parent of {backup}) "
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
				f"{backup.parent} (parent of {backup}) "
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

 # The index list subcommand {{{
class CmdListIndex(CmdLeaf, IndexSelectionOptions, ListRemoteOptions):
	cmd = "list"
	help = "TODO"

	def execute(self) -> None:
		cmd_list_index(self)

def cmd_list_index(args: CmdListIndex) -> None:
	remote_backups = discover_remote_backups(args, keep_index_only=True)

	nbytes = 0
	nindices = 0
	for backup in sorted(remote_backups.values()):
		assert backup.index is not None
		orphaned = len(tuple(backup.all_blobs())) < 2
		if args.orphaned and not orphaned:
			continue

		if orphaned and not args.orphaned:
			print(f"{backup}: orphaned")
		else:
			print(backup)

		nindices += 1
		nbytes += backup.index.size

		if args.verbose:
			created = backup.index.time_created.timestamp()
			print("",
				time.strftime("%Y-%m-%d %H:%M:%S",
					time.localtime(created)),
				humanize_size(backup.index.size),
				sep="\t")

	if args.verbose and nindices > 1:
		print()
		print("%d indices in %s." % (nindices, humanize_size(nbytes)))
# }}}

# The index get subcommand {{{
class CmdGetIndex(CmdLeaf, CommonOptions, DownloadBlobOptions,
			SelectionOptions):
	cmd = "get"
	help = "TODO"

	selection_section = "indexsel"

	output: Optional[str] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["transfer"]
		section.add_argument("--output", "-o")

		self.add_dir()

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		if args.output is not None and args.output != '-':
			self.output = args.output

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		if self.output is None:
			self.progress = None

	def execute(self) -> None:
		cmd_get_index(self)

def cmd_get_index(args: CmdGetIndex) -> None:
	remote_by_uuid = discover_remote_backups(args, keep_index_only=True)
	remote_backups = sorted(remote_by_uuid.values())

	# Figure out what @to_retrieve.
	to_retrieve = choose_snapshots(args, "remotely",
					remote_backups, remote_by_uuid)
	if not to_retrieve:
		print("Nothing to retrieve.",
			file=sys.stderr if self.output is None else sys.stdout)
		return

	output_dir = output = None
	if args.output is not None:
		print("Retrieving the index of:")
		for i in to_retrieve:
			print("  %s" % remote_backups[i])
		print()

		try:
			output = open(args.output, 'w')
		except IsADirectoryError:
			output_dir = args.output
	else:	# sys.stdout is text, but the index could be binary.
		# Just pass it through.
		output = os.fdopen(sys.stdout.fileno(), "wb", closefd=False)

	bytes_transferred = 0
	started = time.monotonic()
	for i in to_retrieve:
		backup = remote_backups[i]
		assert backup.index is not None

		if args.output is not None:
			# @output is not sys.stdout.
			print(f"Retrieving {backup}'s index...", end="", flush=True)
		try:
			if output_dir is not None:
				assert output is None
				output_fname = "%s.lst" % os.path.join(
								output_dir,
								backup.fname)
				output = open(output_fname, 'w')

			bytes_transferred += download_blob(args,
				backup.index, BlobType.INDEX, backup.uuid,
				pipeline_stdout=output)

			if output_dir is not None:
				output.close()
				output = None
		finally:
			if args.output is not None:
				print()

	if output is not None:
		output.close()

	if len(to_retrieve) > 1 and args.output is not None:
		duration = time.monotonic() - started

		print()
		print("Retrieved %d indices (%s) in %s."
			% (len(to_retrieve),
				humanize_size(bytes_transferred),
				humanize_duration(duration)))
# }}}

# The index delete subcommand {{{
class CmdDeleteIndex(CmdLeaf, DeleteOptions, IndexSelectionOptions):
	cmd = "delete"
	help = "TODO"

	bucket_required = True
	selection_section = "indexsel"

	force: bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["force"]
		section.add_enable_flag("--force")

		self.add_dir()

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		if self.orphaned and self.exact:
			raise self.CmdLineError(
				"cannot specify --exact with --orphan")

		self.force = args.force

	def execute(self) -> None:
		cmd_delete_index(self)

def cmd_delete_index(args: CmdDeleteIndex) -> None:
	local_snapshots = \
		uuid_to_snapshots(discover_local_snapshots(args.dir)) \
		if not args.force else None

	remote_by_uuid = discover_remote_backups(args, keep_index_only=True)
	if args.orphaned:
		filter_dict(remote_by_uuid, lambda backup: backup.orphan())
	remote_backups = sorted(remote_by_uuid.values())

	# Figure out what @to_delete.
	to_delete = choose_snapshots(args, "remotely",
					remote_backups, remote_by_uuid)
	if not to_delete:
		print("Nothing to delete.")
		return

	print("Considering to delete the indices of:")
	for i in to_delete:
		print("  %s" % remote_backups[i])
	print()

	# Delete indices.
	ndeleted = 0
	deleted_bytes = 0
	for i in to_delete:
		backup = remote_backups[i]
		blob = backup.index
		assert blob is not None

		if local_snapshots is not None \
				and backup.uuid not in local_snapshots:
			print(f"{backup} is not present locally.")
			continue

		ndeleted += 1
		deleted_bytes += blob.size

		details = [ ]
		if args.show_uuid:
			details.append(str(backup.uuid))
		details.append(humanize_size(blob.size))
		details = ", ".join(details)

		if args.dry_run:
			print("Would delete %s (%s)." % (blob.name, details))
			continue

		print("Deleting %s (%s)..." % (blob.name, details))
		blob.delete()
		backup.clear_blob(BlobType.INDEX)

	if ndeleted > 0:
		print()
		print("%s %d indices (%s)."
			% (woulda(args, "deleted"), ndeleted,
				humanize_size(deleted_bytes)))
	else:
		if to_delete:
			print()
		print("Would not have deleted anything.")
# }}}

# Non-leaf-level subcommands {{{
class CmdList(CmdLineCommand):
	cmd = "list"
	help = "TODO"

	def get_subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdListBuckets(), CmdListLocal(), CmdListRemote())

class CmdDelete(CmdLineCommand):
	cmd = "delete"
	help = "TODO"

	def get_subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdDeleteLocal(), CmdDeleteRemote())

class CmdIndex(CmdLineCommand):
	cmd = "index"
	help = "TODO"

	def get_subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdListIndex(), CmdGetIndex(), CmdDeleteIndex())

# The top-level command.
class CmdTop(CmdLineCommand):
	description = "TODO"

	def get_subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdList(), CmdDelete(), CmdUpload(), CmdDownload(),
			CmdIndex())

	def parse(self) -> CmdLeaf:
		parser = argparse.ArgumentParser(
				description=self.description,
				add_help=False)
		self.build_for_parser(parser)
		args = parser.parse_args()

		# Find which leaf-level CmdLineCommand was called.
		cmd = self
		level = 1
		while True:
			var = f"sub{level}command"
			if not hasattr(args, var):
				break
			cmd = cmd.find_subcommand(getattr(args, var))
			level += 1
		assert isinstance(cmd, CmdLeaf)

		try:
			cmd.setup(args)
		except CmdLineOptions.CmdLineError as ex:
			if cmd.debug:
				raise
			parser.error(ex.args[0])

		return cmd
# }}}

# Main starts here. {{{
cmd = None
try:
	cmd = CmdTop().parse()
	cmd.execute()
except KeyboardInterrupt:
	sys.exit("Interrupted.")
except (FatalError, UserError) as ex:
	if cmd is None or cmd.debug:
		# Print the backtrace when debugging.
		raise
	sys.exit("%s: %s" % (type(ex).__name__, " ".join(ex.args)))
# }}}

# vim: set foldmethod=marker:
# End of giccs.py
