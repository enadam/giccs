#!/usr/bin/python3
#
# TODO: {{{
# args -> self
# DirEnt.volatile -> obj?
# maybe load glob2 on-demand
# Globber: sorting?
# COUNTER_SCRIPT -> dd?
#
# consistency check of remote backups
# calculate/verify hash?
#
# upload/download: split plan and execution
# consider using clone sources when uploading
#
# CmdFTPGet, CmdFTPPut: DryRunOptions, WetRunOptions, AutodeleteOptions?
# CmdFTPGet: --no-keep-mtime
#
# tabbing?
# dynamic discovery
# get, put
# cat [-c <bytes>], page?
# mv [--dir/--fname]
# mkdir, rmdir?
#
# overwrite:
#   * skip
#   * error
#   * ask
#   * force
# overwrite-mode:
#   * truncate
#   * atomic
# put:
#   * skip-enoent-eloop
#   * follow-symlinks
#
# document max blob size (5 TiB)
# document required permissions
#   * storage.objects.create
#   * storage.objects.update (for patch())
#   * storage.buckets.list (for list buckets)
#   * storage.objects.list
#   * storage.objects.get
# document the use of gpg-agent
# document dependency on python3-glob2
#
# protect against:
#   * blob swapping: header
#   * block swapping between blobs: header
#   * block reordering: random sequence number
#   * blob truncation: expected number of blocks
# external encryption must generate and verify the MAC
# }}}

# Modules {{{
from __future__ import annotations

from typing import	TypeVar, Protocol, Self, \
			Any, Union, Optional, Final, \
			Generator, Iterator, Iterable, Callable, \
			Container, Collection, Sequence, \
			TextIO, BinaryIO, ByteString

import sys, os
import io, fcntl, stat
import subprocess
import pathlib, glob2
import time, datetime
import re, bisect, uuid
import base64, binascii
import random, secrets
import argparse, configparser
import enum, dataclasses, struct
import contextlib, functools

import btrfs

sys.path.append("/home/adam/volatile/btrfs/giccs/lib")
import google.cloud.storage
import google.oauth2.service_account
# }}}

# Constants and structures {{{
# A generic-purpose type variable.
T = TypeVar("T")

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
		options: list[Union[
				tuple[Sequence[str], dict[str, Any]],
				Mutex]]

		def __init__(self, name: Optional[str] = None):
			self.name = name
			self.options = [ ]

		# Called by subclasses of CmdLineOptions to add
		# mutually-exclusive options.
		def add_mutually_exclusive_group(self, required=False) \
							-> Mutex:
			mutex = CmdLineOptions.Mutex(required)
			self.options.append(mutex)
			return mutex

		# Called by subclasses of CmdLineOptions to find the last
		# Mutex group in @self.options.
		def last_mutex(self) -> Mutex:
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

		# Called by CmdLineOptions.remove_argument() to remove an
		# argument from @self.options if it's declared in this section.
		def remove_argument(self, flag: str) -> bool:
			for i, option in enumerate(self.options):
				if isinstance(option, CmdLineOptions.Mutex):
					if option.remove_argument(flag):
						return True
				elif flag in option[0]:
					break
			else:
				return False

			del self.options[i]
			return True

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

	# Has setup() been called?
	_setup: bool = False

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

	# Merge options from @args and @self.ini, determine which ones take
	# precedence, and report conflicts.
	#
	# If @options is:
	#	"geez",
	#	("alpha", "beta", "gamma"),
	#	("foo", "bar", "baz"),
	# keys in the same group don't conflict, but keys across groups can
	# conflict if they are specified through the command line or are in
	# the same section of the config file.
	def merge_options_from_ini(
			self, args: argparse.Namespace,
			*options: Sequence[Union[str, tuple[str]]],
			tpe: type = str) -> None:
		def effective_group(groups: Collection[Sequence[str]]) \
				-> Optional[Sequence[str]]:
			if not groups:
				return None
			elif len(groups) == 1:
				# Return groups[0].
				return next(iter(groups))

			groups = [ '/'.join(keys) for keys in groups ]
			last = groups.pop()
			raise self.CmdLineError(
				"conflicting options %s and %s"
				% (", ".join(groups), last))

		groups = { } # key -> ("group", "of", "key")
		values = { } # key -> "value-of-key" | None

		# Were any of the @options specified through the command line?
		cmdline = [ ] # groups of keys set on the command line
		for group in options:
			if not isinstance(group, tuple):
				group = (group,)

			current = None
			for key in group:
				val = getattr(args, key, None)
				if val is not None:
					if current is None:
						current = [ ]
						cmdline.append(current)
					current.append(key)

				groups[key] = group
				values[key] = val
		effective = effective_group(cmdline)

		if self.ini is not None:
			# Collect options set in the @default and @non_default
			# sections of @self.ini.
			default = { }
			non_default = { }
			for key, val in values.items():
				if val is not None:
					# Option set on the @cmdline,
					# ignore the config.
					continue

				# Retrieve the string @val:ue of @key.
				try:
					val = self.ini.get(
						self.config_section, key)
				except configparser.NoSectionError as ex:
					raise self.CmdLineError(
						"%s: %s"
						% (self.ini.filenames[0],
							ex.message)) from ex
				except configparser.NoOptionError:
					continue

				# Add @key to @default or @non_default.
				tier = default if self.ini.is_default(val) \
						else non_default
				tier.setdefault(groups[key], [ ]).append(key)

				# Get the right @val based on @tpe.
				if tpe is bool:
					val = self.ini.getboolean(
						self.config_section, key)
				elif tpe is int:
					val = self.ini.getint(
						self.config_section, key)
				values[key] = val

			if effective is None:
				effective = \
					effective_group(non_default.values())
			if effective is None:
				effective = effective_group(default.values())

		# Propagate the @effective options from the config to @args.
		if effective is not None:
			for key in groups[effective[0]]:
				val = values[key]
				if val is not None:
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
	def shlex_split(self, what: str, s: str, empty_ok: bool = False) \
			-> list[str]:
		import shlex

		what = what.replace('_', '-')
		try:
			lst = shlex.split(s)
		except ValueError as ex:
			raise self.CmdLineError(f"{what}: {ex.args[0]}")

		if not lst and not empty_ok:
			raise self.CmdLineError(f"{what}: missing value")
		return lst

	# Public methods.
	# Remove a previously declared argument.
	def remove_argument(self, flag: str) -> bool:
		for section in self.sections.values():
			if section.remove_argument(flag):
				return True
		return False

	# Add the options declared in @self.sections to @parser.
	def add_arguments(self, parser: argparse.ArgumentParser) -> None:
		for section in self.sections.values():
			section.add_arguments(parser)

	# Set up the object state from command-line arguments.
	def setup(self, args: argparse.Namespace) -> None:
		if self._setup:
			return
		self._setup = True

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
	cmd: Union[str, Sequence[str]]

	help: str
	description: Optional[str] = None

	# Proxy property accesses to this object.
	parent: Optional[CmdLineOptions] = None

	def __init__(self, parent: Optional[CmdLineOptions] = None):
		super().__init__()
		self.parent = parent

	def __getattr__(self, attr: str) -> Any:
		if self.parent is not None:
			try:
				return getattr(self.parent, attr)
			except AttributeError:
				pass

		# Raise an authentic AttributeError.
		self.__getattribute__(attr)
		assert False

	def isa(self, what: str) -> bool:
		if isinstance(self.cmd, str):
			return self.cmd == what
		else:
			return what in self.cmd

	def aliases(self) -> Sequence[str]:
		if isinstance(self.cmd, str):
			return (self.cmd,)
		else:
			return self.cmd

	# Subclasses should cache the list with @functools.cached_property
	# so we have a single instance of the subcommands.
	@property
	def subcommands(self) -> Sequence["CmdLineCommand"]:
		# By default commands don't have subcommands.
		return ()

	def find_subcommand(self, cmd: str) -> CmdLineCommand:
		for subcommand in self.subcommands:
			if subcommand.isa(cmd):
				return subcommand
		raise KeyError(f"{cmd}: subcommand not found")

	def add_arguments(self, parser: argparse.ArgumentParser) -> None:
		# Add --help to all levels of subcommands, but don't include
		# it in the help text itself.
		parser.add_argument("--help", "-h",
			action="help", help=argparse.SUPPRESS)
		super().add_arguments(parser)

	def build_for_subparser(self, subparser, level: int = 1) -> None:
		if isinstance(self.cmd, str):
			cmd, aliases = self.cmd, ()
		else:
			cmd, *aliases = self.cmd

		self.build_for_parser(
				subparser.add_parser(
					cmd,
					aliases=aliases,
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
					required=not isinstance(self, CmdExec),
					metavar="subcommand",
					dest=f"sub{level}command")
		for subcommand in self.subcommands:
			subcommand.build_for_subparser(
					subparser, level + 1)

	def setup(self, args: argparse.Namespace) -> None:
		if self.parent is not None:
			self.parent.setup(args)
		if isinstance(self, CmdExec):
			super().setup(args)
# }}}

# An executable (usually leaf-level) subcommand.
class CmdExec(CmdLineCommand): # {{{
	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["common"]
		section.add_enable_flag_no_dflt("--debug")

	def execute(self) -> None:
		# Subclasses must implement it.
		raise NotImplementedError
# }}}

# An entry point to the command line parser tree.
class CmdTop(CmdLineCommand): # {{{
	# Can be overridden by subclasses.
	class ArgumentParser(argparse.ArgumentParser): pass

	@functools.cached_property
	def debug(self) -> bool:
		debug = os.environ.get("GICCS_DEBUG")
		if debug is None:
			return False

		try:
			return int(debug) > 0
		except ValueError:
			return debug.lower() in ("true", "yes", "on")

	def parse(self, cmdline: Optional[Sequence[str]] = None) -> CmdExec:
		parser = self.ArgumentParser(
				description=self.description,
				add_help=False)
		self.build_for_parser(parser)
		args = parser.parse_args(cmdline)

		if getattr(args, "debug", None):
			# Make sure all future instances of this class
			# has debugging enabled.
			__class__.debug = self.debug = True

		# Find which leaf-level CmdLineCommand was called.
		cmd = self
		level = 1
		while True:
			subcommand = getattr(args, f"sub{level}command", None)
			if subcommand is None:
				break
			cmd = cmd.find_subcommand(subcommand)
			level += 1
		assert isinstance(cmd, CmdExec)

		try:
			cmd.setup(args)
		except CmdLineOptions.CmdLineError as ex:
			if self.debug:
				raise
			parser.error(ex.args[0])

		return cmd

	def run(self, cmdline: Optional[Sequence[str]] = None) -> bool:
		try:
			self.parse(cmdline).execute()
		except KeyboardInterrupt:
			print("Interrupted.", file=sys.stderr)
			raise
		except (FatalError, UserError,
				Globber.MatchError, FileNotFoundError,
				NotADirectoryError, IsADirectoryError) as ex:
			if self.debug:
				# Print the backtrace when debugging.
				import traceback
				traceback.print_exc()
			else:
				msg = ex.args
				if isinstance(msg, (tuple, list)):
					msg = ' '.join(map(str, msg))
				print("%s: %s" % (type(ex).__name__, msg),
	  				file=sys.stderr)
			return False
		else:
			return True
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
	@functools.cached_property
	def gcs_client(self) -> google.cloud.storage.Client:
		if self.service_account_info is not None:
			creds = google.oauth2.service_account.Credentials. \
					from_service_account_info(
						self.service_account_info)
		else:
			creds = None
		return google.cloud.storage.Client(credentials=creds)
# }}}

# Provide options to specify the GCS bucket to use.
class BucketOptions(AccountOptions): # {{{
	# Can be overridden by subclasses.
	bucket_required: bool = False

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
				if val is None:
					continue
				if bucket.labels[key] != val:
					return False

		return True

	# Find the bucket specified on the command line.
	@functools.cached_property
	def bucket(self) -> google.cloud.storage.Bucket:
		if self.bucket_name is not None:
			self.bucket = self.gcs_client.bucket(self.bucket_name)
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
		for bucket in self.gcs_client.list_buckets():
			if self.bucket_matches(bucket):
				found.append(bucket)

		if not found:
			raise UserError("Bucket not found")
		elif len(found) > 1:
			raise UserError("More than one buckets found")
		else:
			return found[0]
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
class SelectionOptions(CmdLineOptions): # {{{
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

	def any_selected(self, args: argparse.Namespace) -> bool:
		return args.all or args.first or args.last \
			or args.frm is not None or args.to is not None \
			or args.exact

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

# Compression {{{
class CompressionOptionsBase(CmdLineOptions):
	DFLT_COMPRESSION	= "xz"
	DFLT_COMPRESSOR		= (DFLT_COMPRESSION, "-c")
	DFLT_DECOMPRESSOR	= (DFLT_COMPRESSION, "-dc")

	compressor:		Optional[Sequence[str]] = None
	decompressor:		Optional[Sequence[str]] = None

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

# Add --compress, --no-compress and --compressor.
class CompressionOptions(CompressionOptionsBase):
	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["compress"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag_no_dflt("--compress", "-Z")
		mutex.add_disable_flag_no_dflt("--no-compress")
		mutex.add_argument("--compressor", dest="compress")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.compressor = \
			self.get_compressor(
				args.compress, "compress",
				"compressor", "decompressor",
				self.DFLT_COMPRESSOR)

# Add --compress-index, --no-compress-index and --index-compressor.
class IndexCompressionOptions(CompressionOptionsBase):
	index_compressor: Optional[Sequence[str]] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["compress"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag_no_dflt("--compress-index")
		mutex.add_disable_flag_no_dflt("--no-compress-index")
		mutex.add_argument("--index-compressor", dest="compress_index")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.index_compressor = \
			self.get_compressor(
				args.compress_index, "compress-index",
				"index-compressor", "index-decompressor",
				self.DFLT_COMPRESSOR, self.DFLT_COMPRESSOR)

# Add --decompress, --no-decompress and --decompressor.
class DecompressionOptions(CompressionOptionsBase):
	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["compress"]
		mutex = section.add_mutually_exclusive_group()

		flags = [ "--decompress" ]
		if not isinstance(self, CompressionOptions):
			flags.append("-Z")
		mutex.add_enable_flag_no_dflt(*flags)

		mutex.add_disable_flag_no_dflt("--no-decompress")
		mutex.add_argument("--decompressor", dest="decompress")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		if self.compressor is not None:
			# CompressionOptions has enabled compression.
			fallback = self.DFLT_DECOMPRESSOR
		else:
			fallback = None
		self.decompressor = \
			self.get_compressor(
				args.decompress, "compress",
				"decompressor", "compressor",
				self.DFLT_DECOMPRESSOR, fallback)

# Add --decompress-index, --no-decompress-index and --index-decompressor.
class IndexDecompressionOptions(CompressionOptionsBase):
	index_decompressor: Optional[Sequence[str]] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["compress"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag_no_dflt("--decompress-index")
		mutex.add_disable_flag_no_dflt("--no-decompress-index")
		mutex.add_argument("--index-decompressor",
					dest="decompress_index")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.index_decompressor = \
			self.get_compressor(
				args.decompress_index, "compress-index",
				"index-decompressor", "index-compressor",
				self.DFLT_DECOMPRESSOR, self.DFLT_DECOMPRESSOR)
# }}}

# Add --encryption-command/--encryption-key/--encryption-key-command/etc.
class EncryptionOptions(CmdLineOptions): # {{{
	encryption_command:	Optional[Sequence[str]] = None
	decryption_command:	Optional[Sequence[str]] = None

	encryption_key:		Optional[bytes] = None
	encryption_key_command:	Optional[Sequence[str]] = None
	encryption_key_per_uuid: bool = False

	encrypt_metadata:	bool = False
	verify_blob_size:	bool = False
	add_header_to_blob:	bool = False

	subvolume: Optional[str] = None

	def encrypt_internal(self) -> bool:
		return self.encryption_key is not None \
				or self.encryption_key_command is not None

	def encrypt_external(self) -> bool:
		return bool(self.encryption_command or self.decryption_command)

	@property
	def encrypt(self):
		return self.encrypt_internal() or self.encrypt_external()

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["bucket"]
		section.add_argument("--subvolume", "-V")

		section = self.sections["encryption"]
		section.add_argument("--encryption-command", "--encrypt")
		mutex = section.add_mutually_exclusive_group()
		mutex.add_argument("--decryption-command", "--decrypt")
		mutex.add_argument("--encryption-key", "--key")
		mutex.add_argument("--encryption-key-command", "--key-cmd")
		section.add_enable_flag_no_dflt("--encryption-key-per-uuid")

		section.add_disable_flag_no_dflt("--no-encrypt-metadata")
		section.add_disable_flag_no_dflt("--no-verify-blob-size")
		section.add_disable_flag_no_dflt("--no-blob-header")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args, "subvolume")
		self.subvolume = args.subvolume

		self.merge_options_from_ini(args,
			("encryption_command", "decryption_command"),
			"encryption_key",
			"encryption_key_command")
		if args.encryption_command is not None:
			# Ensure that neither --encryption-key
			# nor --encryption-key-command is used.
			if args.decryption_command is None:
				raise self.CmdLineError(
					"--encryption-command must be used "
					"together with --decryption-command")
			self.encryption_command = \
				self.shlex_split(
					"encryption-command",
					args.encryption_command)
		if args.decryption_command is not None:
			# For downloads it doesn't matter
			# if --encryption-command is set.
			if args.encryption_command is None \
					and isinstance(
						self, UploadBlobOptions):
				raise self.CmdLineError(
					"--decryption-command must be used "
					"together with --encryption-command")
			self.decryption_command = \
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
		elif not self.encrypt_external():
			# InternalEncrypt always writes a header.
			raise self.CmdLineError(
				"--no-blob-header only makes sense with "
				"--encryption-command/--decryption-command")

class EncryptedBucketOptions(EncryptionOptions, BucketOptions):
	# Initialize @self.subvolume if it hasn't been set explicitly.
	@property
	def bucket(self) -> google.cloud.storage.Bucket:
		bucket = super().bucket

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
			kwargs["retry"] = google.cloud.storage.blob \
						.DEFAULT_RETRY \
						.with_timeout(self.timeout)
		return kwargs
# }}}

# Upload/DownloadBlobOptions {{{
class UploadBlobOptions(CompressionOptionsBase, EncryptionOptions,
			TransferOptions):
	pass

class DownloadBlobOptions(CompressionOptionsBase, EncryptionOptions,
				TransferOptions):
	pass
# }}}

class CommonOptions(EncryptedBucketOptions, AccountOptions, ConfigFileOptions):
	pass

class DeleteOptions(CommonOptions, DryRunOptions, DeleteSelectionOptions):
	pass

# Add --uuid.
class ShowUUIDOptions(CmdLineOptions): # {{{
	show_uuid: Optional[bool] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["display"]
		section.add_enable_flag_no_dflt("--uuid", "-u")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.show_uuid = args.uuid
# }}}

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
	snapshot_name_fmt = re.compile(
				r"^(\d{4}-\d{2}-\d{2})(?:\.(\d+))?(?:_(.*))?$")

	snapshot_name:	str
	snapshot_uuid:	uuid.UUID

	date:		str = dataclasses.field(init=False)
	seq:		Optional[int] = dataclasses.field(init=False)
	tag:		Optional[str] = dataclasses.field(init=False)

	@classmethod
	def parse(self, snapshot_name: str) -> Optional[re.Match]:
		return self.snapshot_name_fmt.fullmatch(snapshot_name)

	# Parse @self.snapshot_name into @self.date, @self.seq and @self.tag.
	def __post_init__(self):
		m = self.parse(self.snapshot_name)
		if m is None:
			raise FatalError(
				f"{self.snapshot_name}: invalid snapshot name")

		self.date = m.group(1)
		self.seq = int(m.group(2)) if m.group(2) is not None else None
		self.tag = m.group(3)

	def matches(self, what: Union[str, uuid.UUID]) -> bool:
		if isinstance(what, uuid.UUID):
			return self.snapshot_uuid == what
		else:
			return self.snapshot_name == what

	def __str__(self) -> str:
		return self.snapshot_name

	def __eq__(self, other: Union[Snapshot, uuid.UUID]) -> bool:
		if isinstance(other, Snapshot):
			other = other.snapshot_uuid
		return self.snapshot_uuid == other

	# Operator for sorting.  @other must be different from @self
	# as an additional measure for consistency.
	def __lt__(self, other: Snapshot) -> bool:
		if self.date < other.date:
			return True
		elif self.date > other.date:
			return False
		elif self.seq is None and other.seq is None:
			raise ConsistencyError(
				"%s and %s have the same date"
				% (self.snapshot_name, other.snapshot_name))
		elif self.seq is None:
			return True
		elif other.seq is None:
			return False
		elif self.seq == other.seq:
			raise ConsistencyError(
				"%s and %s have the same date and seq"
				% (self.snapshot_name, other.snapshot_name))
		else:
			return self.seq < other.seq
# }}}

@dataclasses.dataclass
class Backup(Snapshot): # {{{
	index:	Optional[BackupBlob] = None
	full:	Optional[BackupBlob] = None
	delta:	Optional[BackupBlob] = None

	# Used by Backups.restorable().
	restorable: Optional[bool] = None

	@property
	def parent(self) -> Optional[uuid.UUID]:
		return self.delta.parent_uuid \
			if self.delta is not None \
			else None

	def __init__(self, blob: BackupBlob):
		super().__init__(blob.snapshot_name, blob.snapshot_uuid)
		self.add_blob(blob)

	# Set one of @self.index, @self.full or @self.delta.
	def add_blob(self, blob: BackupBlob) -> None:
		if blob.snapshot_name != self.snapshot_name:
			raise ConsistencyError(
				"%s has unexpected snapshot name (%s != %s)"
				% (blob.name, blob.snapshot_name,
					self.snapshot_name))
		elif blob.snapshot_uuid != self.snapshot_uuid:
			raise ConsistencyError(
				"%s has unexpected snapshot UUID "
				"(%s != %s)"
				% (blob.name, blob.snapshot_uuid,
					self.snapshot_uuid))

		existing = getattr(self, blob.payload_type.field())
		if existing is not None:
			raise ConsistencyError(
				"%s has duplicate %s blobs (%s and %s)"
				% (self, blob.payload_type.field(),
					existing.name, blob.name))

		setattr(self, blob.payload_type.field(), blob)

	def clear_blob(self,
			which: Union[BackupBlob.PayloadType, BackupBlob]) \
			-> None:
		if isinstance(which, BackupBlob):
			which = which.payload_type
		setattr(self, which.field(), None)

	def all_blobs(self) -> Iterable[BackupBlob]:
		return filter(None, (getattr(self, payload_type.field())
					for payload_type
		       			in BackupBlob.PayloadType))

	def orphaned(self) -> bool:
		return not any(
			blob.payload_type != BackupBlob.PayloadType.INDEX
			for blob in self.all_blobs()
		)
# }}}

# A collection of Snapshot:s.
class Snapshots(dict[uuid.UUID, Snapshot]): # {{{
	where: Final[str] = "locally"

	@functools.cached_property
	def ordered(self) -> list[Snapshot]:
		return sorted(self.values())

	def __contains__(self, other: Union[Snapshot, uuid.UUID]) -> bool:
		if isinstance(other, Snapshot):
			other = other.snapshot_uuid
		return super().__contains__(other)

	def __getitem__(self, key: Union[uuid.UUID, int]) -> Snapshot:
		if isinstance(key, int):
			return self.ordered[key]
		else:
			return super().__getitem__(key)

	def __setitem__(self, key: uuid.UUID, val: Snapshot) -> None:
		super().__setitem__(key, val)

		# The property doesn't exist until it's read first.
		try: del self.ordered
		except AttributeError: pass

	def __delitem__(self, key: uuid.UUID) -> None:
		super().__delitem__(key)
		try: del self.ordered
		except AttributeError: pass

	def add(self, snapshot: Snapshot) -> None:
		self[snapshot.snapshot_uuid] = snapshot

	def remove(self, snapshot: Snapshot) -> None:
		del self[snapshot.snapshot_uuid]

	# Return the index of a Snapshot.
	def find(self, what: Union[str, uuid.UUID]) -> int:
		if isinstance(what, uuid.UUID):
			# Get @snapshot_name from UUID.
			try:
				snapshot_name = self[what].snapshot_name
			except KeyError:
				raise UserError(
					f"{what} not found {self.where}")
		else:
			snapshot_name = what

		i = bisect.bisect_left(self, snapshot_name,
			 key=lambda snapshot: snapshot.snapshot_name)
		if i < len(self) and self[i].snapshot_name == snapshot_name:
			return i
		raise UserError(f"{what} not found {self.where}")
# }}}

# A collection of Backup:s.
class Backups(Snapshots): # {{{
	where: Final[str] = "remotely"

	@functools.cached_property
	def blobs(self) -> dict[uuid.UUID, BackupBlob]:
		# This method is only supposed to be called if encryption
		# is on, so all blobs should have a @blob.blob_uuid.
		return {
			blob.blob_uuid: blob
			for backup in self.values()
			for blob in backup.all_blobs()
			if blob.blob_uuid is not None
		}

	# Does the Backup identified by its UUID or any of its parents have
	# a full backup?
	def restorable(self, snapshot_uuid: Optional[uuid.UUID]) -> bool:
		# Use a non-recursive algorithm to scale arbitrarily.
		backups = [ ]
		restorable = None
		while True:
			if snapshot_uuid is None:
				break

			backup = self.get(snapshot_uuid)
			if backup is None:
				break

			restorable = backup.restorable
			if restorable is not None:
				break

			backups.append(backup)
			if backup.full is not None:
				restorable = True
				break
			snapshot_uuid = backup.parent

		# Cache the result.
		restorable = restorable is True
		for backup in backups:
			backup.restorable = restorable

		return restorable
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
	#   1) an UUID unambiguously identifying the blob it belongs to
	#   2) a pseudo-random sequence number unique for each ciphertext;
	#      the first block contains the seed, from which the sequence
	#      number of the remaining blocks are derived.
	#
	# 1) protects against swapping ciphertext blocks between blobs
	# (or swapping entire blobs with each other) while 2) prevents
	# the reordering of blocks within a Backup.
	#
	# Calculating a MAC for the whole blob would be less secure because
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
	inbytes: int
	outbytes: int

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
		self.inbytes = self.outbytes = 0

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

	def read(self, n: Optional[int] = None) \
			-> Union[memoryview, bytearray]:
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
			self.outbytes += len(ciphertext)
			return ciphertext

		if self.ciphertext_i > 0:
			try:
				del self.ciphertext[:self.ciphertext_i]
			except BufferError:
				# There could be an "Existing exports of data:
				# object cannot be re-sized" error if a view
				# of self.ciphertext returned earlier is still
				# held somewhere in the program.
				self.ciphertext = \
					self.ciphertext[self.ciphertext_i:]
			self.ciphertext_i = 0

		while n is None or len(self.ciphertext) < n:
			cleartext = self.newbuf()
			minbuf = len(cleartext)

			while len(cleartext) < self.CLEARTEXT_SIZE \
					and not self.eof:
				prev = len(cleartext)
				cleartext += self.wrapped.read(
						self.CLEARTEXT_SIZE - prev)
				self.inbytes += len(cleartext) - prev
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
			self.outbytes += len(ciphertext)
			return ciphertext
		else:
			ciphertext = memoryview(self.ciphertext)[:n]
			self.ciphertext_i = n
			self.outbytes += len(ciphertext)
			return ciphertext

class InternalDecrypt(InternalCipher):
	nonce: Optional[bytearray]
	prng: Optional[random.Random]
	ciphertext: bytearray

	def __init__(self, key: bytes,
			data_type_id: Optional[int] = None,
			blob_uuid: Optional[uuid.UUID] = None,
			wrapped: Optional[BinaryIO] = None):
		super().__init__(key, data_type_id, blob_uuid, wrapped)

		self.nonce = None
		self.prng = None
		self.ciphertext = bytearray()

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

# A class abstracting the details of encryption away.
class MetaCipher: # {{{
	class DataType(enum.IntEnum):
		PAYLOAD		= 0
		SIGNATURE	= 1
		SUBVOLUME	= 2
		BLOB_PATH	= 3
		BLOB_SIZE	= 4
		FILE_SIZE	= 5
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

	# Like InternalCipher.header_st, but for external encryption.
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
		key = subprocess_check_output(
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

	CipherClass = TypeVar("CipherClass", bound=InternalCipher)
	def internal_cipher(self, cipher_class: type[CipherClass],
				data_type: DataType, wrapped: BinaryIO) \
				-> CipherClass:
		assert self.args.encrypt_internal()
		return cipher_class(self.get_encryption_key(),
					data_type.value, self.blob_uuid,
					wrapped=wrapped)

	def internal_encrypt(self, data_type: DataType, src: BinaryIO) \
				-> InternalEncrypt:
		return self.internal_cipher(InternalEncrypt, data_type, src)

	def internal_decrypt(self, data_type: DataType, dst: BinaryIO) \
				-> InternalDecrypt:
		return self.internal_cipher(InternalDecrypt, data_type, dst)

	def external_cipher(self, cipher_cmd: Sequence[str]) -> dict[str, Any]:
		assert self.args.encrypt_external()
		return {
			"args": cipher_cmd,
			"env": self.get_cipher_cmd_env(),
		}

	def external_encrypt(self) -> dict[str, Any]:
		assert self.args.encryption_command is not None
		return self.external_cipher(self.args.encryption_command)

	def external_decrypt(self) -> dict[str, Any]:
		assert self.args.decryption_command is not None
		return self.external_cipher(self.args.decryption_command)

	def external_header(self, data_type: DataType) -> bytes:
		return self.external_header_st.pack(
					data_type.value,
					ensure_uuid(self.blob_uuid).bytes)

	def encrypt(self, data_type: DataType, cleartext: bytes) \
			-> Union[memoryview, bytearray, bytes]:
		if self.args.encrypt_internal():
			return self.internal_encrypt(
					data_type,
					io.BytesIO(cleartext)).read()
		else:	# @self.args.add_header_to_blob is pointedly ignored
			# for the meaningful security of metadata.
			header = self.external_header(data_type)
			return subprocess_check_output(
				**self.external_encrypt(),
				input=header + cleartext)

	def decrypt(self, data_type: DataType, ciphertext: bytes) \
			-> memoryview:
		if self.args.encrypt_internal():
			cleartext = io.BytesIO()
			cipher = self.internal_decrypt(data_type, cleartext)
			cipher.write(ciphertext)
			cipher.close()

			if self.blob_uuid is None:
				self.blob_uuid = cipher.blob_uuid

			return cleartext.getbuffer()

		# External encryption.
		cleartext = memoryview(subprocess_check_output(
				**self.external_decrypt(),
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
# }}}

# A GCS blob with metadata.
class MetaBlob(MetaCipher): # {{{
	T = TypeVar("MetaBlobType", bound=Self)

	# hashlib doesn't define an abstract base class, let's have our own.
	class Hasher(Protocol):
		def update(self, data: bytes) -> None:
			...

		def digest(self) -> bytes:
			...

	gcs_blob: google.cloud.storage.Blob

	blob_path: str
	blob_size: Optional[int]
	file_size: Optional[int]

	# Whether metadata has changed.
	dirty: bool = False

	@property
	def name(self) -> str:
		return self.gcs_blob.name

	@property
	def subvolume(self) -> str:
		return self.args.subvolume

	# This is a context manager, so we can perform things post-__init__().
	@contextlib.contextmanager
	def new(self: T, args: EncryptedBucketOptions, path: str,
			backups: Optional[Backups] = None) \
			-> contextlib.AbstractContextManager[T]:
		super().__init__(args)

		while True:
			if args.encrypt:
				# Generate a random @self.blob_uuid.
				self.blob_uuid = uuid.uuid4()

			if args.encrypt_metadata:
				blob_name = str(self.blob_uuid)
			else:
				blob_name = path
			if args.prefix is not None:
				blob_name = f"{args.prefix}/{blob_name}"

			self.gcs_blob = args.bucket.blob(blob_name)
			if not args.encrypt:
				assert self.blob_uuid is None
				break
			elif backups is not None \
					and self.blob_uuid in backups.blobs:
				# The generated @self.blob_uuid conflicts
				# with an existing one.
				continue
			elif backups is None and args.encrypt_metadata \
					and self.gcs_blob.exists():
				# Likewise.
				continue
			else:
				break

		self.set_metadata(self.DataType.SUBVOLUME, self.subvolume)
		self.set_metadata(self.DataType.BLOB_PATH, path)
		self.blob_size = None

		# Return control to the caller.
		yield self

		self.update_signature()
		self.dirty = False

	# Used if the caller just wants a new MetaBlob.  Shouldn't be called
	# from subclasses.
	def __init__(self, args: EncryptedBucketOptions, path: str):
		with self.new(args, path):
			pass

	# Like above, but allows for customizing the initialization.
	@classmethod
	def create(cls: type[T], args: EncryptedBucketOptions, path: str) \
			-> contextlib.AbstractContextManager[T]:
		self = super().__new__(cls)
		return self.new(args, path)

	# Create a MetaBlob from and existing @gcs_blob.
	@classmethod
	def init(cls: type[T], args: EncryptedBucketOptions,
			gcs_blob: google.cloud.storage.Blob) -> T:
		self = super().__new__(cls)
		super().__init__(self, args)

		self.gcs_blob = gcs_blob
		if args.prefix is not None:
			prefix = args.prefix + '/'
			if not self.name.startswith(prefix):
				raise ConsistencyError(
					f"{self.name} doesn't start with "
					f"{prefix}")
			prefixless = self.name.removeprefix(prefix)
		else:
			prefixless = self.name

		signature = None
		if args.encrypt_metadata:
			blob_uuid = prefixless
			try:
				self.blob_uuid = uuid.UUID(blob_uuid)
			except ValueError as ex:
				raise ConsistencyError(
					f"{self.name} has invalid UUID "
					f"({blob_uuid})") from ex

			self.blob_path = self.get_metadata(
						self.DataType.BLOB_PATH)
		elif args.encrypt:
			# Retrieving the metadata should set @self.blob_uuid.
			# It's safe to use an encrypted hash as a MAC as long
			# as the underlying cipher is non-malleable, which is
			# the case with InternalCipher, being AEAD.
			signature = self.get_metadata(self.DataType.SIGNATURE)
			assert self.blob_uuid is not None

			self.blob_path = self.get_metadata(
						self.DataType.BLOB_PATH)
			if prefixless != self.blob_path:
				raise SecurityError(
					"%s has unexpected path, should be %s"
					% (self.name, self.blob_path))
		else:
			self.blob_path = prefixless

		self.setup()

		if args.verify_blob_size or self.has_metadata(
						self.DataType.BLOB_SIZE):
			self.blob_size = self.get_metadata(
						self.DataType.BLOB_SIZE)
			if gcs_blob.size != self.blob_size:
				raise SecurityError(
					"%s has unexpected size (%d != %d)"
					% (self.name, gcs_blob.size,
						self.blob_size))
		else:
			self.blob_size = None

		if self.has_metadata(self.DataType.FILE_SIZE):
			self.file_size = self.get_metadata(
						self.DataType.FILE_SIZE)
		else:
			self.file_size = None

		if signature is not None:
			if signature != self.calc_signature().digest():
				raise SecurityError(
					f"{self.name} has invalid signature")
		elif self.has_metadata(self.DataType.SIGNATURE):
			# Possible misconfiguration.
			raise ConsistencyError(
				"%s[%s]: unexpected metadata"
				% (self.name, self.DataType.SIGNATURE.field()))

		# Return None if @gcs_blob doesn't belong to the backups
		# of @args.subsystem after all.
		if self.get_metadata(self.DataType.SUBVOLUME) \
				!= self.subvolume:
			return None
		return self

	# Called by init().
	def setup(self) -> None:
		pass

	def __str__(self):
		return self.blob_path

	def encode_int(self, value: Optional[int], width: int = 8) -> bytes:
		if value is None:
			value = (1 << 8*width) - 1
		return value.to_bytes(8, "big")

	def decode_int(self, value: bytes) -> int:
		return int.from_bytes(value, "big")

	def calc_signature(self) -> Hasher:
		import hashlib

		# SHA-256 is fast and secure.
		hasher = hashlib.sha256()

		hasher.update(self.subvolume.encode())
		hasher.update(b'\0')

		hasher.update(self.blob_path.encode())
		hasher.update(b'\0')

		hasher.update(self.encode_int(self.blob_size))
		hasher.update(self.encode_int(self.file_size))

		return hasher

	def has_metadata(self, data_type: MetaCipher.DataType) -> bool:
		return self.gcs_blob.metadata \
			and data_type.field() in self.gcs_blob.metadata

	def get_raw_metadata(self, data_type: MetaCipher.DataType) -> str:
		# TypeError is raised if self.gcs_blob.metadata is None.
		try:
			return self.gcs_blob.metadata[data_type.field()]
		except (TypeError, KeyError):
			raise SecurityError(
				"%s[%s]: missing metadata"
				% (self.name, data_type.field()))

	def set_raw_metadata(self, data_type: MetaCipher.DataType,
				metadata: str) -> None:
		# To update @self.gcs_blob.metadata we need to assign
		# a new dict.
		new_metadata = self.gcs_blob.metadata
		if new_metadata is None:
			new_metadata = { }
		new_metadata[data_type.field()] = metadata

		self.gcs_blob.metadata = new_metadata
		self.dirty = True

	def decode_metadata(self, data_type: MetaCipher.DataType,
				metadata: str) -> bytes:
		try:
			return base64.b64decode(metadata, validate=True)
		except binascii.Error as ex:
			raise SecurityError(
				"%s[%s]: couldn't decode metadata"
				% (self.name, data_type.field())) from ex

	def encode_metadata(self, data_type: MetaCipher.DataType,
				metadata: bytes) -> str:
		return base64.b64encode(metadata).decode()

	def decrypt_metadata(self, data_type: MetaCipher.DataType,
				metadata: str) -> bytes:
		ciphertext = self.decode_metadata(data_type, metadata)
		try:
			return bytes(self.decrypt(data_type, ciphertext))
		except FatalError as ex:
			raise ex.__class__(
				"%s[%s]:" % (self.name, data_type.field()),
				*ex.args) from ex

	def encrypt_metadata(self, data_type: MetaCipher.DataType,
				metadata: bytes) -> str:
		return self.encode_metadata(
			data_type, self.encrypt(data_type, metadata))

	def get_binary_metadata(self, data_type: MetaCipher.DataType) -> bytes:
		# The signature is always encrypted.
		metadata = self.get_raw_metadata(data_type)
		if not self.args.encrypt_metadata \
				and data_type != self.DataType.SIGNATURE:
			return self.decode_metadata(data_type, metadata)
		else:
			return self.decrypt_metadata(data_type, metadata)

	def set_binary_metadata(self, data_type: MetaCipher.DataType,
				value: bytes) -> None:
		# Like above.
		if not self.args.encrypt_metadata \
				and data_type != self.DataType.SIGNATURE:
			metadata = self.encode_metadata(data_type, value)
		else:
			metadata = self.encrypt_metadata(data_type, value)
		self.set_raw_metadata(data_type, metadata)

	def get_text_metadata(self, data_type: MetaCipher.DataType) -> str:
		metadata = self.get_raw_metadata(data_type)
		if not self.args.encrypt_metadata:
			return metadata

		metadata = self.decrypt_metadata(data_type, metadata)
		try:
			return metadata.decode()
		except ValueError as ex:
			raise SecurityError(
				"%s[%s]: invalid metadata"
				% (self.name, data_type.field())) from ex

	def set_text_metadata(self, data_type: MetaCipher.DataType,
				value: str) -> None:
		if not self.args.encrypt_metadata:
			metadata = value
		else:
			metadata = self.encrypt_metadata(
					data_type, value.encode())
		self.set_raw_metadata(data_type, metadata)

	def get_integer_metadata(self, data_type: MetaCipher.DataType,
					width: int = 8) -> int:
		metadata = self.get_raw_metadata(data_type)

		if not self.args.encrypt_metadata:
			try:
				return int(metadata)
			except ValueError as ex:
				raise SecurityError(
					"%s[%s]: invalid metadata"
					% (self.name, data_type.field())) \
					from ex

		metadata = self.decrypt_metadata(data_type, metadata)
		if len(metadata) != width:
			raise SecurityError(
				"%s[%s]: unexpected metadata size (%d != %d)"
				% (self.name, data_type.field(),
					len(metadata), width))
		return self.decode_int(metadata)

	def set_integer_metadata(self, data_type: MetaCipher.DataType,
					value: int, width: int = 8) -> None:
		if not self.args.encrypt_metadata:
			metadata = str(value)
		else:
			metadata = self.encrypt_metadata(
					data_type,
					self.encode_int(value, width))
		self.set_raw_metadata(data_type, metadata)

	def get_uuid_metadata(self, data_type: MetaCipher.DataType) \
				-> uuid.UUID:
		metadata = self.get_raw_metadata(data_type)

		if not self.args.encrypt_metadata:
			try:
				return uuid.UUID(metadata)
			except ValueError as ex:
				raise SecurityError(
					"%s[%s]: invalid metadata"
					% (self.name, data_type.field())) \
					from ex

		metadata = self.decrypt_metadata(data_type, metadata)
		try:
			return uuid.UUID(bytes=metadata)
		except ValueError as ex:
			raise SecurityError(
				"%s[%s]: invalid metadata"
				% (self.name, data_type.field())) from ex

	def set_uuid_metadata(self, data_type: MetaCipher.DataType,
			value: uuid.UUID) -> None:
		if not self.args.encrypt_metadata:
			metadata = str(value)
		else:
			metadata = self.encrypt_metadata(
					data_type, value.bytes)
		self.set_raw_metadata(data_type, metadata)

	def get_metadata(self, data_type: MetaCipher.DataType) -> Any:
		if data_type == self.DataType.SIGNATURE:
			return self.get_binary_metadata(data_type)
		elif data_type == self.DataType.SUBVOLUME:
			return self.get_text_metadata(data_type)
		elif data_type == self.DataType.BLOB_PATH:
			return self.get_text_metadata(data_type)
		elif data_type == self.DataType.BLOB_SIZE:
			return self.get_integer_metadata(data_type)
		elif data_type == self.DataType.FILE_SIZE:
			return self.get_integer_metadata(data_type)
		else:
			assert False

	def set_metadata(self, data_type: MetaCipher.DataType, value: T) -> T:
		if data_type == self.DataType.SIGNATURE:
			self.set_binary_metadata(data_type, value)
		elif data_type == self.DataType.SUBVOLUME:
			self.set_text_metadata(data_type, value)
		elif data_type == self.DataType.BLOB_PATH:
			# If not @self.args.encrypt, this is redundant.
			# Otherwise if not @self.args.encrypt_metadata,
			# it's still validated.
			if self.args.encrypt:
				self.set_text_metadata(data_type, value)
			self.blob_path = value
		elif data_type == self.DataType.BLOB_SIZE:
			if self.args.verify_blob_size:
				self.set_integer_metadata(data_type, value)
				self.blob_size = value
		elif data_type == self.DataType.FILE_SIZE:
			self.set_integer_metadata(data_type, value)
			self.file_size = value
		else:
			assert False
		return value

	def update_signature(self):
		if self.args.encrypt and not self.args.encrypt_metadata:
			self.set_metadata(
					self.DataType.SIGNATURE,
					self.calc_signature().digest())

	def sync_metadata(self):
		if self.dirty:
			self.update_signature()
			self.gcs_blob.patch()
			self.dirty = False
# }}}

# A MetaBlob of a Backup.
class BackupBlob(MetaBlob): # {{{
	@enum.unique
	class PayloadType(enum.IntEnum):
		INDEX	= 0
		FULL	= 1
		DELTA	= 2

		def field(self):
			return self.name.lower()

	payload_type: PayloadType
	snapshot_name: str
	snapshot_uuid: uuid.UUID
	parent_uuid: Optional[uuid.UUID]

	def __init__(self, args: EncryptedBucketOptions,
	      		payload_type: PayloadType,
			snapshot: Snapshot, parent: Optional[Snapshot],
	      		backups: Backups):
		with self.new(args, "%s/%s" % (snapshot.snapshot_name,
						 payload_type.field()),
				backups):
			self.set_metadata(self.DataType.SNAPSHOT_UUID,
		     				snapshot.snapshot_uuid)
			if payload_type == self.PayloadType.DELTA:
				assert parent is not None
				self.set_metadata(self.DataType.PARENT_UUID,
							parent.snapshot_uuid)
			else:
				assert parent is None
				self.parent_uuid = None

	def setup(self) -> None:
		self.snapshot_name, per, payload_type = \
				self.blob_path.rpartition('/')
		if not per:
			raise ConsistencyError(
				f"{self.name}'s path is missing "
				"payload type")

		if not payload_type.islower():
			raise ConsistencyError(
				f"{self.name}'s path has invalid "
				f"payload type ({payload_type})")
		payload_type = payload_type.upper()
		try:
			self.payload_type = self.PayloadType[payload_type]
		except KeyError:
			raise ConsistencyError(
				f"{self.name} has unknown "
				f"payload type ({payload_type})")

		self.snapshot_uuid = self.get_metadata(
						self.DataType.SNAPSHOT_UUID)
		if self.payload_type == self.PayloadType.DELTA:
			self.parent_uuid = self.get_metadata(
						self.DataType.PARENT_UUID)
		elif self.has_metadata(self.DataType.PARENT_UUID):
			raise ConsistencyError(
				"%s[%s]: unexpected metadata"
				% (self.name,
					self.DataType.PARENT_UUID.field()))
		else:
			self.parent_uuid = None

	def calc_signature(self) -> MetaBlob.Hasher:
		hasher = super().calc_signature()

		hasher.update(self.snapshot_uuid.bytes)
		hasher.update(ensure_uuid(self.parent_uuid).bytes)

		return hasher

	def get_metadata(self, data_type: MetaCipher.DataType) -> Any:
		if data_type == self.DataType.SNAPSHOT_UUID:
			return self.get_uuid_metadata(data_type)
		elif data_type == self.DataType.PARENT_UUID:
			return self.get_uuid_metadata(data_type)
		else:
			return super().get_metadata(data_type)

	def set_metadata(self, data_type: MetaCipher.DataType, value: T) -> T:
		if data_type == self.DataType.SNAPSHOT_UUID:
			self.set_uuid_metadata(data_type, value)
			self.snapshot_uuid = value
		elif data_type == self.DataType.PARENT_UUID:
			self.set_uuid_metadata(data_type, value)
			self.parent_uuid = value
		else:
			return super().set_metadata(data_type, value)
		return value
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

# Store the size of multiple MetaBlob:s.
class SizeAccumulator: # {{{
	_blob_size: Optional[int] = None
	_blob_size_incomplete: bool = False

	_file_size: Optional[int] = None
	_file_size_incomplete: bool = False

	def __init__(self, init: Optional[Union[int, MetaBlob]] = None):
		if isinstance(init, int):
			self._blob_size = init
		elif isinstance(init, MetaBlob):
			self.add(init)

	def _add(self, attr: str, value: Optional[int]) -> None:
		if value is None:
			setattr(self, f"{attr}_incomplete", True)
		elif getattr(self, attr) is None:
			setattr(self, attr, value)
		else:
			setattr(self, attr, getattr(self, attr) + value)

	def add(self, what: Union[Self, MetaBlob]) -> None:
		if isinstance(what, self.__class__):
			self._add("_blob_size", what._blob_size)
			self._blob_size_incomplete |= \
					what._blob_size_incomplete
			self._add("_file_size", what._file_size)
			self._file_size_incomplete |= \
					what._file_size_incomplete
		else:
			self._add("_blob_size", what.gcs_blob.size)
			self._add("_file_size", what.file_size)

	def _get(self, attr: str, **kw) -> Optional[int]:
		value = getattr(self, attr)
		if value is None:
			return None

		value = humanize_size(value, **kw)
		if getattr(self, f"{attr}_incomplete"):
			value += '+'
		return value

	def blob_size(self, **kw) -> Optional[str]:
		return self._get("_blob_size")

	def file_size(self, **kw) -> Optional[str]:
		return self._get("_file_size")

	def get(self, **kw) -> Optional[str]:
		blob_size = self.blob_size(**kw)
		if blob_size is None:
			return None
		sizes = [ blob_size ]

		file_size = self.file_size(**kw)
		if file_size is not None:
			sizes.append(file_size)

		return '/'.join(sizes)
# }}}

# A chain of subprocesses.  When the Pipeline is deleted, its subprocesses
# are killed.
class Pipeline: # {{{
	# Allow it to be an int for subprocess.PIPE and DEVNULL.
	StdioType = Union[int, io.IOBase]

	_stdin: Optional[StdioType]
	_stdout: Optional[StdioType]

	def __init__(self,
			cmds: Sequence[Union[Sequence[str], dict[str, Any]]],
			stdin: Optional[StdioType] = subprocess.DEVNULL,
			stdout: Optional[StdioType] = None):
		if isinstance(stdin, int):
			assert stdin < 0
		if isinstance(stdout, int):
			assert stdout < 0

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

# glob.glob() on steroids.
class Globber(glob2.Globber): # {{{
	# Raised by glob() when it finds no or too many matches unexpectedly.
	class MatchError(Exception): pass

	# List of globbing metacharacters.
	GLOBBING = ('?', '*', '[', ']')

	# The GLOBBING characters may be escaped like this in patterns.
	escaped = re.compile(r"\\(.)")

	def has_magic(self, pattern: str) -> bool:
		# Remove the escaped metacharacters from the @pattern
		# to make glob2.has_magic() more accurate.
		return glob2.has_magic(self.escaped.sub("", pattern))

	def must_exist(self, path: str) -> None:
		os.stat(path)

	# If @at_least_one and @at_most_one, return a single string.
	def glob(self, pattern: str,
			at_least_one: bool = True,
	  		must_exist: bool = True,
			at_most_one: bool = False) -> Union[Iterable[str], str]:
		def subst(m: re.Match) -> str:
			# This is how to escape metacharacters for glob2.glob().
			c = m.group(1)
			return f"[{c}]" if c in self.GLOBBING else c
		matches = super().iglob(self.escaped.sub(subst, pattern))

		if not at_least_one and not at_most_one:
			# We can return the iterator directly.
			return matches

		matches = list(matches)
		if at_least_one and not matches:
			if self.has_magic(pattern):
				raise self.MatchError(f"{pattern}: no matches")
			elif must_exist:
				# Raise the appropriate exception.
				self.must_exist(pattern)
				assert False
			elif at_most_one:
				return pattern
			else:
				return (pattern,)
		elif at_most_one and len(matches) > 1:
			raise self.MatchError(f"{pattern}: too many matches")

		if at_least_one and at_most_one:
			assert len(matches) == 1
			return matches[0]
		else:
			return matches

	def globs(self, patterns: Iterable[str], **kw) -> Iterable[str]:
		for pattern in patterns:
			matches = self.glob(pattern, **kw)
			if isinstance(matches, str):
				yield matches
			else:
				yield from matches
# }}}

# A virtual file system.
class VirtualGlobber(Globber): # {{{
	@dataclasses.dataclass
	class DirEnt:
		fname: str
		children: Optional[dict[str, DirEnt]] = None
		parent: Optional[DirEnt] = None

		# Whether this entry was created on-demand by _lookup().
		volatile: bool = False

		# Any associated object, eg. a MetaBlob.
		obj: Any = None

		@classmethod
		def mkfile(cls, fname: str, obj: Any = None,
				volatile: bool = False) -> DirEnt:
			return cls(fname, None, obj=obj, volatile=volatile)

		@classmethod
		def mkdir(cls, fname: str, obj: Any = None,
				volatile: bool = False) -> DirEnt:
			return cls(fname, { }, obj=obj, volatile=volatile)

		def __lt__(self, other: DirEnt) -> bool:
			return self.fname < other.fname

		def __eq__(self, other: DirEnt) -> bool:
			return id(self) == id(other)

		def __hash__(self) -> int:
			return id(self)

		def __repr__(self) -> str:
			parent = self.parent
			if parent is not None:
				parent = "..."

			children = self.children
			if children is not None:
				children = "..."

			return "%s(fname=%r, children=%s, parent=%s)" \
				% (self.__class__.__name__, self.fname,
       					children, parent)

		def path(self, relative_to: Optional[DirEnt] = None) \
				-> pathlib.PurePath:
			parts = [ ]
			dent = self
			while dent is not relative_to:
				parts.append(dent.fname)
				if dent.parent is None:
					break
				dent = dent.parent
			return pathlib.PurePath(*reversed(parts))

		def isdir(self):
			return self.children is not None

		def must_be_dir(self) -> None:
			if not self.isdir():
				raise NotADirectoryError(self.path())

		def is_parent(self, parent: DirEnt) -> bool:
			dent = self
			while True:
				if dent is parent:
					return True
				dent = dent.parent
				if dent is None:
					return False

		def __iter__(self) -> Iterator[Self]:
			self.must_be_dir()
			return iter(sorted(self.children.values()))

		def __contains__(self, fname: str) -> bool:
			self.must_be_dir()
			return fname in self.children

		def __getitem__(self, fname: str) -> DirEnt:
			self.must_be_dir()
			child = self.children.get(fname)
			if child is None:
				raise FileNotFoundError(
					self.path().joinpath(fname))
			return child

		def get(self, fname: str) -> Optional[DirEnt]:
			self.must_be_dir()
			return self.children.get(fname)

		def add(self, child: DirEnt) -> DirEnt:
			assert child.parent is None
			self.must_be_dir()

			if child.fname in self.children:
				raise FileExistsError(
					self.path() / child.fname)

			self.children[child.fname] = child
			child.parent = self

			return child

		def remove(self, child: DirEnt) -> DirEnt:
			self.must_be_dir()
			del self.children[child.fname]
			child.parent = None
			return child

		def infanticide(self) -> None:
			self.must_be_dir()
			for child in self:
				child.parent = None
			self.children = { }

		def ls(self) -> Iterable[str]:
			self.must_be_dir()
			return sorted(self.children.keys())

		def scan(self, include_self: bool = True) -> Iterator[DirEnt]:
			if include_self:
				yield self
			if self.isdir():
				for child in self:
					yield from child.scan()

		# Remove this entry's branch if it's volatile.
		def rollback(self) -> None:
			if not self.volatile:
				return

			child, parent = self, self.parent
			while parent.volatile:
				child, parent = parent, parent.parent
			parent.remove(child)

	root: DirEnt
	cwd: DirEnt

	def __init__(self, files: Iterable[Any]):
		self.cwd = self.root = self.DirEnt.mkdir('/')
		for file in files:
			parent = self.root
			path = pathlib.PurePath(str(file))
			start = 1 if path.is_absolute() else 0
			for fname in path.parts[start:-1]:
				child = parent.get(fname)
				if child is None:
					child = self.DirEnt.mkdir(fname)
					parent.add(child)
				parent = child
			parent.add(self.DirEnt.mkfile(path.parts[-1], file))

	def lookup(self, path: str, create: bool = False) -> DirEnt:
		return self._lookup(self.escaped.sub(r"\1", path), create)

	def _lookup(self, path: str, create: bool = False) -> DirEnt:
		if not path:
			raise FileNotFoundError(path)

		must_be_dir = path.endswith(('/', "/."))
		path = pathlib.PurePath(path)
		if path.is_absolute():
			parts = path.parts[1:]
			dent = self.root
		else:
			parts = path.parts
			dent = self.cwd

		for i, fname in enumerate(parts):
			dent.must_be_dir()
			if fname != "..":
				try:
					dent = dent[fname]
				except FileNotFoundError:
					if not create:
						raise

					parent = dent
					leaf = i == len(parts) - 1

					dent = self.DirEnt.mkdir(
							fname, volatile=True) \
						if not leaf or must_be_dir \
						else self.DirEnt.mkfile(
							fname, volatile=True)
					parent.add(dent)
			elif dent.parent is not None:
				dent = dent.parent
		if must_be_dir:
			dent.must_be_dir()

		return dent

	def chdir(self, path: str) -> None:
		dent = self._lookup(path)
		dent.must_be_dir()
		self.cwd = dent

	def listdir(self, path: str) -> list[str]:
		return self._lookup(path).ls()

	def isdir(self, path: str) -> bool:
		return self._lookup(path).isdir()

	def islink(self, path: str) -> bool:
		return False

	def must_exist(self, path: str) -> None:
		self._lookup(path)

	def exists(self, path: str) -> bool:
		try:
			self.must_exist(path)
		except (FileNotFoundError, NotADirectoryError):
			return False
		else:
			return True
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

# Wrapper around subprocess.check_output() that handles exceptions.
def subprocess_check_output(*args, **kwargs) -> bytes:
	try:
		return subprocess.check_output(*args, **kwargs)
	except subprocess.CalledProcessError as ex:
		# Conceal the arguments, they might be sensitive.
		ex.cmd = ex.cmd[0]
		raise FatalError(str(ex)) from ex

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
def humanize_size(size: int, with_exact=False) -> str:
	if size < 1024:
		return str(size) if with_exact else f"{size} B"

	exact = size
	for unit in ("KiB", "MiB", "GiB", "TiB", "PiB"):
		size /= 1024.0
		if size < 1024:
			break

	human = "%.2f %s" % (size, unit)
	return f"{exact} ({human})" if with_exact else human

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

# Blob-related functions {{{
def discover_remote_blobs(args: EncryptedBucketOptions,
				cls: type[MetaBlob.T] = MetaBlob) \
				-> Iterable[MetaBlob.T]:
	prefix = args.prefix
	if prefix is not None:
		prefix += '/'

	for blob in args.bucket.list_blobs(prefix=prefix):
		if (blob := cls.init(args, blob)) is not None:
			yield blob

# Write @blob.blob_uuid as binary to @sys.stdout.
def write_header(blob: MetaBlob) -> Callable[[], None]:
	def write_header():
		# Redirect this function's stdout to stderr, so it doesn't
		# go into the pipeline by accident.
		stdout, sys.stdout = sys.stdout, sys.stderr

		try:
			os.write(
				stdout.fileno(),
				blob.external_header(blob.DataType.PAYLOAD))
		except Exception as ex:
			# The contents of exceptions are not passed back
			# to the main interpreter, so let's print it here.
			print(ex, file=sys.stderr)
			raise

	return write_header

# Pump stdin to stdout while counting the number of bytes transferred,
# written to the file descriptor designated by the first argument.
COUNTER_SCRIPT = """
import sys, os

n = 0
while True:
	buf = os.read(sys.stdin.fileno(), 1024*1024)
	if not buf:
		break
	os.write(sys.stdout.fileno(), buf)
	n += len(buf)
open(int(sys.argv[1]), 'w').write(str(n))
"""

def upload_blob(args: UploadBlobOptions, blob: MetaBlob,
		command: Optional[Sequence[str]] = None,
		pipeline_stdin: Optional[Pipeline.StdioType] = None,
		count_bytes_in: bool = True, wet_run: bool = False,
		overwrite: Optional[bool] = None) -> int:
	assert command is not None or pipeline_stdin is not None

	if args.encrypt_external() and args.add_header_to_blob:
		# Write @blob_uuid into the pipeline before the @command
		# is executed.  We rely on the pipe having capacity for
		# ~16 bytes, otherwise there will be a deadlock.
		#
		# If we're using InternalEncrypt, it will add the headers
		# itself.
		command = {
			"args": command or ("cat",),
			"preexec_fn": write_header(blob),
		}

	pipeline = [ ]
	if command is not None:
		pipeline.append(command)
	if args.compressor is not None:
		pipeline.append(args.compressor)
	if args.encrypt_external():
		pipeline.append(blob.external_encrypt())

	bytes_in_counter = None
	if pipeline and (command is None or len(pipeline) > 1) \
			and count_bytes_in:
		if not isinstance(pipeline_stdin, io.IOBase):
			# Insert @bytes_in_counter after the @command,
			# counting its output.
			assert command is not None
			bytes_in_counter = { }
			pipeline.insert(1, bytes_in_counter)
		elif stat.S_ISREG(os.stat(pipeline_stdin.fileno()).st_mode):
			# We don't need to count the file size, just retrieve
			# it when we're done (who knows, it might change
			# meanwhile).
			bytes_in_counter = pipeline_stdin
		else:	# Insert @bytes_in_counter before anything else.
			# counting @pipeline_stdin.
			bytes_in_counter = { }
			pipeline.insert(0, bytes_in_counter)

		if isinstance(bytes_in_counter, dict):
			r, w = os.pipe()
			bytes_in_counter["executable"] = sys.executable
			bytes_in_counter["args"] = \
				("python3", "-c", COUNTER_SCRIPT, str(w))
			bytes_in_counter["pass_fds"] = (w,)
			bytes_in_counter = (r, w)

	# @pipeline could be empty.
	kw = { "stdout": subprocess.PIPE }
	if pipeline_stdin is not None:
		kw["stdin"] = pipeline_stdin
	pipeline = Pipeline(pipeline, **kw)

	if isinstance(bytes_in_counter, tuple):
		r, w = bytes_in_counter
		os.close(w)
		bytes_in_counter = r

	src = pipeline.stdout()
	if args.encrypt_internal():
		src = blob.internal_encrypt(blob.DataType.PAYLOAD, src)
		if count_bytes_in and bytes_in_counter is None:
			bytes_in_counter = src

	# Check the @pipeline for errors before returning the last read
	# to upload_from_file().  If pipeline.wait() throws an exception
	# the upload will fail and not create the blob.
	src = Progressometer(src, args.progress, final_cb=pipeline.wait)
	if count_bytes_in and bytes_in_counter is None:
		bytes_in_counter = src

	if not wet_run:
		try:
			flags = args.get_retry_flags()
			if overwrite is True:
				# The blob to update must exist.
				flags["if_generation_not_match"] = 0
			elif overwrite is False:
				# The blob must not exist yet.
				flags["if_generation_match"] = 0
			if args.upload_chunk_size is not None:
				blob.gcs_blob.chunk_size = \
					args.upload_chunk_size * 1024 * 1024
			blob.gcs_blob.upload_from_file(src, checksum="md5",
							**flags)
		except google.api_core.exceptions.PreconditionFailed as ex:
			if overwrite is True:
				raise ConsistencyError(
					"%s does not exist in bucket"
					% blob.name) from ex
			elif overwrite is False:
				raise ConsistencyError(
					"%s already exists in bucket"
					% blob.name) from ex
			else:
				raise
		except GoogleAPICallError as ex:
			raise FatalError(ex) from ex
	else:	# In case of --wet-run just read @src until we hit EOF.
		if overwrite is not None:
			exists = blob.gcs_blob.bucket.get_blob(blob.name) \
					is not None
			if exists and not overwrite:
				raise ConsistencyError(
					"%s already exists in bucket"
					% blob.name)
			elif overwrite and not exists:
				raise ConsistencyError(
					"%s does not exist in bucket"
					% blob.name)
		while src.read(1024*1024):
			pass

	src.final_progress()

	if not wet_run and blob.gcs_blob.size != src.bytes_transferred:
		# GCS has a different idea about the blob's size than us.
		try:
			blob.gcs_blob.delete()
		except:	# We may not have permission to do so.
			print(f"WARNING: {blob.name} could be corrupted, "
				"but unable to delete it!", file=sys.stderr)
		raise ConsistencyError(
				"Blob size mismatch (%d != %d)"
				% (blob.gcs_blob.size, src.bytes_transferred))

	if bytes_in_counter is not None:
		if isinstance(bytes_in_counter, io.IOBase):
			bytes_in = os.stat(pipeline_stdin.fileno()).st_size
		elif isinstance(bytes_in_counter, int):
			bytes_in = int(open(bytes_in_counter).readline())
		elif isinstance(bytes_in_counter, InternalEncrypt):
			bytes_in = bytes_in_counter.inbytes
		elif isinstance(bytes_in_counter, Progressometer):
			bytes_in = bytes_in_counter.bytes_transferred
		else:
			assert False
		blob.set_metadata(blob.DataType.FILE_SIZE, bytes_in)

	blob.set_metadata(blob.DataType.BLOB_SIZE, src.bytes_transferred)
	if not wet_run:
		# In case of failure the blob won't be usable without
		# --no-verify-blob-size, so it's okay not to delete it.
		blob.sync_metadata()

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
expected_data_type = int(sys.argv[1])
expected_uuid = uuid.UUID(sys.argv[2])

# Read and parse the @header.
encryption_header_st = struct.Struct("{encryption_header_st}")
header = os.read(sys.stdin.fileno(), encryption_header_st.size)
if len(header) < encryption_header_st.size:
	sys.exit("Failed to read encryption header, only got %d bytes."
			% len(header))
recv_data_type, recv_uuid = encryption_header_st.unpack_from(header)

# Verify the @header.
if recv_data_type != expected_data_type:
	sys.exit("Data type ID (0x%.2X) differs from expected (0x%.2X)."
			% (recv_data_type, expected_data_type))

if recv_uuid != expected_uuid.bytes:
	sys.exit("Blob UUID (%s) differs from expected (%s)."
			% (uuid.UUID(bytes=recv_uuid), expected_uuid))

# Execute btrfs receive.
os.execvp(sys.argv[3], sys.argv[3:])
""".format(encryption_header_st=MetaCipher.external_header_st.format)

def download_blob(args: DownloadBlobOptions, blob: MetaBlob,
		command: Union[None, Sequence[str], dict[str, Any]] = None,
		pipeline_stdout: Optional[Pipeline.StdioType] = None,
		pipeline_callback:
			Optional[Callable[[Pipeline], None]] = None) -> int:
	assert command is not None or pipeline_stdout is not None

	if args.encrypt_external() and args.add_header_to_blob:
		# Wrap @command with the @HEADER_VERIFICATION_SCRIPT,
		# and pass it the expected DataType and UUID.
		if command is None:
			command_args = ("cat",)
		elif isinstance(command, dict):
			command_args = command["args"]
		else:
			command_args = command

		if not isinstance(command, dict):
			command = { }
		command["executable"] = sys.executable
		command["args"] = \
			("python3", "-c", HEADER_VERIFICATION_SCRIPT,
				str(blob.DataType.PAYLOAD.value),
				str(blob.blob_uuid)) \
			+ command_args

	pipeline = [ ]
	if args.encrypt_external():
		pipeline.append(blob.external_decrypt())
	if args.decompressor is not None:
		pipeline.append(args.decompressor)
	if command is not None:
		pipeline.append(command)

	# @pipeline could be empty.
	pipeline = Pipeline(pipeline,
				stdin=subprocess.PIPE,
				stdout=pipeline_stdout)

	dst = pipeline.stdin()
	if args.encrypt_internal():
		dst = blob.internal_decrypt(blob.DataType.PAYLOAD, dst)

	dst = Progressometer(dst, args.progress, blob.gcs_blob.size)

	try:	# The actual download.
		blob.gcs_blob.download_to_file(dst, **args.get_retry_flags())
		dst.final_progress()
		if isinstance(dst.wrapped, InternalDecrypt):
			dst.wrapped.close()
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

	# It should be safe to wait for the @pipeline now that it has been
	# read.  If it wasn't, we could deadlock.
	pipeline.wait()

	# If there's a mismatch Progressometer.final_progress() should have
	# caught it.
	assert dst.bytes_transferred == blob.gcs_blob.size
	return dst.bytes_transferred
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
		delete_subvol(fs, snapshot.snapshot_name)
# }}}

# Snapshot-related functions {{{
# Go through the direct subdirectories of @path and return Snapshot:s
# for found subvolumes.
def discover_local_snapshots(path: str) -> Snapshots:
	snapshots = Snapshots()
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
			snapshot = Snapshot(dent.name, subvol_uuid(dent.path))
		except OSError:
			# Not on a btrfs file system to begin with.
			pass
		else:
			snapshots.add(snapshot)
	return snapshots
# }}}

# Backup-related functions {{{
# Go through the blobs of a GCS bucket and create Backup:s from them.
def discover_remote_backups(args: EncryptedBucketOptions,
				keep_index_only: bool = False) -> Backups:
	by_name = { }
	by_uuid = Backups()
	for blob in discover_remote_blobs(args, BackupBlob):
		try:
			backup = by_uuid[blob.snapshot_uuid]
		except KeyError:
			backup = Backup(blob)
			existing = by_name.get(backup.snapshot_name)
			if existing is not None:
				raise ConsistencyError(
					"%s and %s have different UUIDs, "
					"but conflicting snapshot names"
					% (blob.name, existing))
			by_uuid[backup.snapshot_uuid] = backup
			by_name[backup.snapshot_name] = backup
		else:
			backup.add_blob(blob)

	if keep_index_only:
		# Keep only Backup:s with an index.
		predicate = lambda backup: backup.index is not None
	else:	# Delete orphaned Backup:s.
		predicate = lambda backup: not backup.orphaned()
	filter_dict(by_uuid, predicate)

	return by_uuid
# }}}

# Snapshot selection {{{
# Return the indexes of multiple --exact snapshots.
def choose_exact_snapshots(args: SelectionOptions,
				snapshots: Snapshots,
				indexes: list[int]) -> bool:
	if not args.exact:
		return False
	assert not args.first and args.frm is None and args.to is None

	# Return the @indexes of @exacts in @snapshots.
	exacts = set(args.exact)
	for i, snapshot in enumerate(snapshots.ordered):
		try:
			if args.use_uuid:
				exacts.remove(snapshot.snapshot_uuid)
			else:
				exacts.remove(snapshot.snapshot_name)
		except KeyError:
			pass
		else:
			indexes.append(i)
			if not exacts:
				break

	if exacts:
		# There are some @exacts we didn't find in @snapshots.
		errors = [ "The following items were not found %s:"
				% snapshots.where ]
		errors += (f"  {exact}" for exact in exacts)
		raise UserError("\n".join(errors))

	return True

# Return the index of the first and last snapshots selected by
# --first/--from/--to.
def choose_snapshot_range(args: SelectionOptions, snapshots: Snapshots) \
				-> tuple[Optional[int], Optional[int]]:
	assert not args.exact

	# Determine the @first and @last snapshots in the range.
	if args.first:
		first = 0
	elif args.frm is not None:
		first = snapshots.find(args.frm)
	else:	# It depends on the caller.
		first = None

	if args.to is not None:
		last = snapshots.find(args.to)
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
def choose_snapshots(args: SelectionOptions, snapshots: Snapshots) \
			-> Collection[int]:
	exacts = [ ]
	if choose_exact_snapshots(args, snapshots, exacts):
		return exacts

	first, last = choose_snapshot_range(args, snapshots)
	if first is not None:
		assert last is not None
		return range(first, last+1)
	elif last is not None:
		return range(last+1)
	else:	# @first and @last are None.
		return ()
# }}}

# The list buckets subcommand {{{
class CmdListBuckets(CmdExec, CommonOptions):
	cmd = "buckets"
	help = "TODO"

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.add_dir()

	def execute(self) -> None:
		cmd_list_buckets(self)

def cmd_list_buckets(args: CmdListBuckets) -> None:
	found = False
	for bucket in args.gcs_client.list_buckets():
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
class CmdListLocal(CmdExec, CommonOptions, ShowUUIDOptions):
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
	backups = discover_remote_backups(args) if args.check_remote else None
	for snapshot in discover_local_snapshots(args.dir).ordered:
		line = [ ]
		if args.show_uuid:
			line.append(snapshot.snapshot_uuid)
		line.append(snapshot)

		if backups is None:
			pass
		elif snapshot in backups:
			line.append("(present remotely)")
		else:
			line.append("(absent remotely)")

		print(*line)
# }}}

 # The list remote subcommand {{{
class CmdListRemote(CmdExec, ListRemoteOptions):
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
	snapshots = discover_local_snapshots(args.dir) \
			if args.dir is not None else None

	nbackups = 0
	nbytes = SizeAccumulator()
	for backup in discover_remote_backups(args).ordered:
		line = [ ]
		if args.show_uuid:
			line.append(backup.snapshot_uuid)
		line.append(backup)

		if snapshots is None:
			pass
		elif backup in snapshots:
			line.append("(present locally)")
		else:
			line.append("(absent locally)")

		print(*line)

		for blob in backup.all_blobs():
			if blob.payload_type in (
					blob.PayloadType.FULL,
					blob.PayloadType.DELTA):
				nbackups += 1
				nbytes.add(blob)

			if args.verbose:
				created = blob.gcs_blob \
						.time_created.timestamp()
				print("", blob.payload_type.field(),
					time.strftime("%Y-%m-%d %H:%M:%S",
						time.localtime(created)),
	  				SizeAccumulator(blob).get(), blob.name,
					sep="\t")

	if args.verbose and nbackups > 1:
		print()
		print("%d backups in %s." % (nbackups, nbytes.get()))
# }}}

# The delete local subcommand {{{
class CmdDeleteLocal(CmdExec, DeleteOptions, SnapshotSelectionOptions):
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

		section = self.sections["operation"]
		section.add_enable_flag("--FLUSH", dest="flush")

		self.add_dir()

	def pre_validate(self, args: argparse.Namespace) -> None:
		# Set defaults for --FLUSH.
		if args.flush:
			if not self.any_selected(args):
				args.first = args.last = True
			if not args.force and not args.force_all:
				args.force_all = True

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

def cmd_delete_local(args: CmdDeleteLocal) -> None:
	snapshots = discover_local_snapshots(args.dir)

	# We don't need to consider the remote @backups if --force-all.
	if not args.force_all:
		backups = discover_remote_backups(args)

	# Figure out what @to_delete.
	to_delete = choose_snapshots(args, snapshots)
	if not to_delete:
		print("Nothing to delete. (Wrong directory?)")
		return

	print("Considering to delete:")
	for i in to_delete:
		print(f"  {snapshots[i]}")
	print()

	# Delete snapshots.
	ndeleted = 0
	fs = OpenDir(args.dir)
	for i in to_delete:
		snapshot = snapshots[i]
		if not args.force_all:
			assert backups is not None
			if not backups.restorable(snapshot.snapshot_uuid):
				print("%s is not restorable from backups, "
					"skipping." % snapshot)
				continue
			elif args.force:
				pass
			elif i+1 < len(snapshots):
				child = snapshots[i+1]
				if child not in backups:
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
class CmdDeleteRemote(CmdExec, DeleteOptions):
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
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag("--delete-full")
		mutex.add_enable_flag("--delete-delta")
		mutex.add_enable_flag("--delete-delta-broken")
		mutex.add_enable_flag("--delete-full-delta")
		mutex.add_enable_flag("--delete-delta-full")

		section = self.sections["force"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag("--force")
		mutex.add_enable_flag("--force-all")

		section = self.sections["operation"]
		section.add_enable_flag("--FLUSH", dest="flush")

		self.add_dir()

	def pre_validate(self, args: argparse.Namespace) -> None:
		delete_any = args.delete_full \
				or args.delete_delta \
				or args.delete_delta_broken \
				or args.delete_full_delta \
				or args.delete_delta_full

		# Set defaults for --FLUSH.
		if args.flush:
			if not self.any_selected(args):
				args.first = args.last = True
			if not delete_any:
				delete_any = args.delete_full_delta = True
			if not args.force and not args.force_all:
				args.force_all = True

		super().pre_validate(args)

		self.force = args.force
		self.force_all = args.force_all
		force = self.force or self.force_all

		if not delete_any:
			raise self.CmdLineError(
				"either of --delete-full/--delete-delta/"
				"--delete-full-delta/--delete-delta-full/"
				"--delete-delta-broken is required")
		elif args.delete_delta_broken and force:
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
	# Only take the local @snapshots into account if --force:d.
	snapshots = discover_local_snapshots(args.dir) \
			if args.force else Snapshots()
	backups = discover_remote_backups(args)

	# Figure out what @to_delete.
	to_delete = choose_snapshots(args, backups)
	if not to_delete:
		print("Nothing to delete.")
		return

	print("Considering to delete:")
	for i in to_delete:
		print(f"  {backups[i]}")
	print()

	# Delete snapshots.
	ndeleted = 0
	deleted_bytes = 0
	for i in to_delete:
		backup = backups[i]

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
		which_to_delete: list[tuple[Optional[BackupBlob], str]] = [ ]
		if args.force_all or backup in snapshots:
			# --force or --force-all
			reason = "snapshot is present locally" \
				if not args.force_all else None
			if args.delete_full:
				which_to_delete.append((backup.full, reason))
			if args.delete_delta:
				which_to_delete.append((backup.delta, reason))
		elif args.prefer_delta and backup.full is not None:
			which_to_delete.append((backup.delta,
						"full backup is available"))
		elif backups.restorable(backup.parent):
			if args.prefer_full:
				which_to_delete.append((
					backup.full,
					"backup is restorable incrementally"))
		else:	# Not restorable from delta.
			if args.delete_delta or args.delete_delta_broken:
				which_to_delete.append((
					backup.delta,
					"incremental backup chain is broken"))

		prev_ndeleted = ndeleted
		for blob, reason in which_to_delete:
			if blob is None:
				continue

			ndeleted += 1
			deleted_bytes += blob.gcs_blob.size

			details = [ humanize_size(blob.gcs_blob.size) ]
			if reason is not None:
				details.append(reason)
			details = ", ".join(details)

			if args.dry_run:
				print(f"Would delete {blob} ({details}).")
				continue

			print(f"Deleting {blob} ({details})...")
			blob.gcs_blob.delete()
			backup.clear_blob(blob)

		# Delete @backup.index if we've deleted all backups.
		if ndeleted > prev_ndeleted and backup.index is not None \
				and backup.orphaned():
			blob = backup.index
			deleted_bytes += blob.gcs_blob.size

			print(f"Deleting {blob}...")
			blob.gcs_blob.delete()

	if ndeleted > 0:
		print()
		print("%s %d backups(s) (%s)."
			% (woulda(args, "deleted"), ndeleted,
				humanize_size(deleted_bytes)))
	else:
		print("Would not have deleted anything.")
# }}}

 # The index list subcommand {{{
class CmdListIndex(CmdExec, IndexSelectionOptions, ListRemoteOptions):
	cmd = "list"
	help = "TODO"

	def execute(self) -> None:
		cmd_list_index(self)

def cmd_list_index(args: CmdListIndex) -> None:
	backups = discover_remote_backups(args, keep_index_only=True)

	nbytes = 0
	nindexes = 0
	for backup in backups.ordered:
		orphaned = backup.orphaned()
		if args.orphaned and not orphaned:
			continue

		if orphaned and not args.orphaned:
			print(f"{backup}: orphaned")
		else:
			print(backup)

		nindexes += 1
		nbytes += backup.index.gcs_blob.size

		if args.verbose:
			created = backup.index.gcs_blob \
					.time_created.timestamp()
			print("",
				time.strftime("%Y-%m-%d %H:%M:%S",
					time.localtime(created)),
				humanize_size(backup.index.gcs_blob.size),
				sep="\t")

	if args.verbose and nindexes > 1:
		print()
		print("%d indexes in %s." % (nindexes, humanize_size(nbytes)))
# }}}

# The index get subcommand {{{
class CmdGetIndex(CmdExec, CommonOptions, DownloadBlobOptions,
			IndexDecompressionOptions, SelectionOptions):
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
	backups = discover_remote_backups(args, keep_index_only=True)

	# Figure out what @to_retrieve.
	to_retrieve = choose_snapshots(args, backups)
	if not to_retrieve:
		print("Nothing to retrieve.",
			file=sys.stderr if self.output is None else sys.stdout)
		return

	output_dir = output = None
	if args.output is not None:
		print("Retrieving the index of:")
		for i in to_retrieve:
			print(f"  {backups[i]}")
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
		backup = backups[i]
		assert backup.index is not None

		if args.output is not None:
			# @output is not sys.stdout.
			print(f"Retrieving {backup}'s index...",
				end="", flush=True)
		try:
			if output_dir is not None:
				assert output is None
				output_fname = f"{backup.snapshot_name}.lst"
				output_path = \
					os.path.join(output_dir, output_fname)
				output = open(output_path, 'w')

			with args.override_flags(
					decompressor=args.index_decompressor):
				bytes_transferred += download_blob(
							args, backup.index,
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
		print("Retrieved %d indexes (%s) in %s."
			% (len(to_retrieve),
				humanize_size(bytes_transferred),
				humanize_duration(duration)))
# }}}

# The index delete subcommand {{{
class CmdDeleteIndex(CmdExec, DeleteOptions, IndexSelectionOptions):
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
				"cannot specify --exact with --orphaned")

		self.force = args.force

	def execute(self) -> None:
		cmd_delete_index(self)

def cmd_delete_index(args: CmdDeleteIndex) -> None:
	snapshots = discover_local_snapshots(args.dir) \
			if not args.force else None

	backups = discover_remote_backups(args, keep_index_only=True)
	if args.orphaned:
		filter_dict(backups, lambda backup: backup.orphaned())

	# Figure out what @to_delete.
	to_delete = choose_snapshots(args, backups)
	if not to_delete:
		print("Nothing to delete.")
		return

	print("Considering to delete the indexes of:")
	for i in to_delete:
		print(f"  {backups[i]}")
	print()

	# Delete indexes.
	ndeleted = 0
	deleted_bytes = 0
	for i in to_delete:
		backup = backups[i]
		blob = backup.index
		assert blob is not None

		if snapshots is not None and backup not in snapshots:
			print(f"{backup} is not present locally.")
			continue

		ndeleted += 1
		deleted_bytes += blob.gcs_blob.size
		details = humanize_size(blob.gcs_blob.size)

		if args.dry_run:
			print(f"Would delete {blob} ({details}).")
			continue

		print(f"Deleting {blob} ({details})...")
		blob.gcs_blob.delete()
		backup.clear_blob(blob)

	if ndeleted > 0:
		print()
		print("%s %d indexes (%s)."
			% (woulda(args, "deleted"), ndeleted,
				humanize_size(deleted_bytes)))
	else:
		if to_delete:
			print()
		print("Would not have deleted anything.")
# }}}

# The upload subcommand {{{
class CmdUpload(CmdExec, UploadDownloadOptions, UploadBlobOptions,
		IndexCompressionOptions, CompressionOptions,
		SnapshotSelectionOptions):
	cmd = "upload"
	help = "TODO"

	selection_section = "snapshot"

	reupload: bool = False
	store_snapshot_size: bool = True
	ignore_remote: bool = False
	index: Optional[bool] = None

	@property
	def overwrite(self) -> Optional[bool]:
		return None if self.ignore_remote else self.reupload

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["upload"]
		section.add_enable_flag("--reupload")
		section.add_disable_flag("--no-store-snapshot-size")

		section = self.sections["operation"]
		section.add_enable_flag("--ignore-remote")

		section = self.sections["index"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag_no_dflt("--index")
		mutex.add_disable_flag_no_dflt("--no-index")
		section.add_argument("--indexer")
		section.add_argument("--index-fmt")

		self.add_dir()

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.store_snapshot_size = args.store_snapshot_size

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

def upload_index(args: CmdUpload, snapshot: Snapshot, backups: Backups) \
			-> int:
	if args.dry_run:
		print(f"Would upload {snapshot}'s index.")
		return 0

	print(f"Uploading {snapshot}'s index...", end="", flush=True)
	try:
		backup = backups.get(snapshot.snapshot_uuid)
		if backup is not None and backup.index is not None:
			blob = backup.index
		else:
			blob = BackupBlob(args, BackupBlob.PayloadType.INDEX,
						snapshot, None, backups)

		# Substitute {snapshot_dir} and {index_fmt} in args.indexer.
		snapshot_dir = os.path.join(args.dir, snapshot.snapshot_name)
		def transformer(arg: str) -> str:
			return arg.format(
				snapshot_dir=snapshot_dir,
				index_fmt=args.index_fmt)
		cmd = tuple(map(transformer, args.indexer))

		with args.override_flags(compressor=args.index_compressor):
			return upload_blob(args, blob, cmd,
						wet_run=args.wet_run,
						overwrite=args.overwrite)
	finally:
		print()

def upload_snapshot(args: CmdUpload, blob: MetaBlob,
			btrfs_send: Sequence[str]) -> int:
	if args.wet_run_no_data:
		btrfs_send = (*btrfs_send, "--no-data")
	return upload_blob(args, blob, btrfs_send,
				count_bytes_in=args.store_snapshot_size,
				wet_run=args.wet_run,
				overwrite=args.overwrite)

def upload_full(args: CmdUpload, snapshot: Snapshot, backups: Backups) -> int:
	if args.dry_run:
		print(f"Would upload {snapshot} in full.")
		return 0

	print(f"Uploading {snapshot} in full...", end="", flush=True)
	try:
		backup = backups.get(snapshot.snapshot_uuid)
		if backup is not None and backup.full is not None:
			blob = backup.full
		else:
			blob = BackupBlob(args, BackupBlob.PayloadType.FULL,
						snapshot, None, backups)

		cmd = ("btrfs", "-q", "send", os.path.join(
			args.dir, snapshot.snapshot_name))
		return upload_snapshot(args, blob, cmd)
	finally:
		print()

def upload_delta(args: CmdUpload, snapshot: Snapshot, parent: Snapshot,
			backups: Backups) -> int:
	if args.dry_run:
		print(f"Would upload {snapshot} delta from {parent}.")
		return 0

	print(f"Uploading {snapshot} delta from {parent}...",
		end="", flush=True)
	try:
		backup = backups.get(snapshot.snapshot_uuid)
		if backup is not None and backup.delta is not None:
			blob = backup.delta
		else:
			blob = BackupBlob(args, BackupBlob.PayloadType.DELTA,
						snapshot, parent, backups)

		cmd = ("btrfs", "-q", "send",
			"-p", os.path.join(args.dir, parent.snapshot_name),
			os.path.join(args.dir, snapshot.snapshot_name))

		return upload_snapshot(args, blob, cmd)
	finally:
		print()

def cmd_upload(args: CmdUpload) -> None:
	snapshots = discover_local_snapshots(args.dir)
	backups = discover_remote_backups(args) \
			if not args.ignore_remote else Backups()

	# Figure out what @to_upload.
	to_upload = [ ]
	if args.reupload:
		# Only reupload what is already present remotely.
		if not choose_exact_snapshots(args, backups, to_upload):
			first, last = choose_snapshot_range(args, backups)
			if last is None:
				print("Nothing to upload.")
				return
			if first is None:
				first = 0
			to_upload = range(first, last+1)

		# Translate indexes from @backups to indexes in @snapshots
		# and verify the ordering.
		fun = lambda i: snapshots.find(backups[i].snapshot_uuid)
		to_upload = list(map(fun, to_upload))
		assert all(lhs < rhs for lhs, rhs
				in zip(to_upload, to_upload[1:]))
	elif not choose_exact_snapshots(args, snapshots, to_upload):
		first, last = choose_snapshot_range(args, snapshots)
		if last is None:
			print("Nothing to upload. (Wrong directory?)")
			return
		if first is None:
			# Choose the @first snapshot to upload.
			if args.prefer_full or args.force_full:
				# Just upload the @last in full.
				first = last
			else:	# Find the @first @snapshot in the remote
				# @backups from the @last one backwards.
				for first in range(last, -1, -1):
					if snapshots[first] in backups:
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
		print(f"  {snapshots[i]}")
	print()

	fs = OpenDir(args.dir) if args.autodelete else None
	prev_uploaded = None
	ndeleted = 0

	# Upload snapshots.
	bytes_transferred = 0
	snapshots_transferred = 0
	started = time.monotonic()
	for i in to_upload:
		snapshot = snapshots[i]
		backup = backups.get(snapshot.snapshot_uuid)
		if i > 0 and snapshots[i-1] in backups:
			parent = snapshots[i-1]
			parent_uuid = parent.snapshot_uuid
			if backup is not None and backup.parent is not None \
					and backup.parent != parent_uuid:
				# @parent is not the parent of @snapshot
				# (it's missing from the local @snapshots).
				parent = None
		else:	# We can't upload a delta.
			parent = None

		# @should_upload_full or @should_upload_delta?
		should_upload_full = should_upload_delta = False
		if args.reupload:
			# User could only select @backup:s from @backups.
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
					msg = "Parent of %s " \
						"not found locally" % backup
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
			bytes_transferred += upload_full(args,
						snapshot, backups)
			snapshots_transferred += 1
		if should_upload_delta:
			assert parent is not None
			bytes_transferred += upload_delta(args,
						snapshot, parent, backups)
			snapshots_transferred += 1
		if should_upload_full or should_upload_delta:
			backups.add(snapshot)
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
			bytes_transferred += upload_index(args,
						snapshot, backups)

		# --autodelete
		if prev_uploaded is not None:
			assert prev_uploaded is not snapshots[-1]
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
class CmdDownload(CmdExec, DownloadBlobOptions, UploadDownloadOptions,
			DecompressionOptions):
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

def download_backup(args: CmdDownload, fname: str,
			blob: google.cloud.storage.Blob,
			btrfs_recv: Sequence[str]) -> int:
	if not args.ignore_local and os.path.exists(
					os.path.join(args.dir, fname)):
		raise UserError(f"{fname} already exists")

	pipeline_stdout = None
	if not args.wet_run:
		# We'll need to parse @btrfs_recv's output.
		btrfs_recv = { "args": btrfs_recv }
		if blob.payload_type == blob.PayloadType.FULL:
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
		if blob.payload_type == blob.PayloadType.FULL:
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
		ret = download_blob(args, blob, btrfs_recv, pipeline_stdout,
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
		return ret

def download_full(args: CmdDownload, backup: Backup) -> int:
	size = humanize_size(backup.full.gcs_blob.size)
	if args.dry_run:
		print(f"Would download {backup} in full ({size}).")
		return backup.full.gcs_blob.size

	print(f"Downloading {backup} in full ({size})...", end="", flush=True)
	try:
		return download_backup(args,
					backup.snapshot_name, backup.full,
					("btrfs", "receive", args.dir))
	finally:
		print()

def download_delta(args: CmdDownload, backup: Backup,
			parent: Snapshot) -> int:
	size = humanize_size(backup.delta.gcs_blob.size)
	if args.dry_run:
		print(f"Would download {backup} delta from {parent} ({size}).")
		return backup.delta.gcs_blob.size

	print(f"Downloading {backup} delta from {parent} ({size})...",
		end="", flush=True)
	try:
		return download_backup(args,
					backup.snapshot_name, backup.delta,
					("btrfs", "receive", args.dir))
	finally:
		print()

def cmd_download(args: CmdDownload) -> None:
	snapshots = discover_local_snapshots(args.dir) \
			if not args.ignore_local else Snapshots()
	backups = discover_remote_backups(args)

	# Validate the parent-child relationships in @backups.
	for i, backup in enumerate(backups.ordered):
		if backup.parent is None:
			continue
		parent = backups.get(backup.parent)
		if parent is None:
			continue
		if i == 0 or parent != backups[i-1]:
			raise ConsistencyError("%s has invalid parent %s"
						% (backup, parent))

	# Figure out what @to_download.
	to_download = [ ]
	if choose_exact_snapshots(args, backups, to_download):
		to_download = [ backups[i] for i in to_download ]
	else:
		first, last = choose_snapshot_range(args, backups)
		if last is None:
			print("Nothing to download.")
			return
		if first is not None:
			to_download = [ backups[i] for i
					in range(first, last+1) ]
		elif args.force_full:
			# If it doesn't have a full backup an error
			# will be thrown later.
			to_download = [ backups[last] ]
		else:	# Choose the @first backup to download.
			first_full = None
			to_download = [ ]
			backup = backups[last]
			while backup is not None:
				to_download.insert(0, backup)
				if backup in snapshots:
					break
				if backup.full is not None \
						and not args.force_delta:
					if args.prefer_full:
						# Start downloading
						# from this @backup.
						break
					elif first_full is None:
						first_full = len(to_download)
				backup = backups.get(backup.parent)

			if backup is None and first_full is not None:
				# Didn't find any @backup in the local
				# @snapshots.  Start downloading with
				# the @first_full.
				del to_download[0:-first_full]

	print("Considering to download:")
	for backup in to_download:
		print(f"  {backup}")
	print()

	fs = OpenDir(args.dir) if args.autodelete else None
	prev_downloaded = None

	# Download backups.
	bytes_transferred = 0
	backups_transferred = 0
	started = time.monotonic()
	for backup in to_download:
		if backup in snapshots:
			print(f"Subvolume for {backup} already exists.")
			continue

		if backup.parent is not None:
			parent = snapshots.get(backup.parent)
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
		snapshots.add(backup)

		bytes_transferred += n
		backups_transferred += 1

		# --autodelete
		if prev_downloaded is not None:
			delete_snapshot(args, fs, prev_downloaded)
			snapshots.remove(prev_downloaded)
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

class FTPClient:
	# Matches the root (/), current (.) and parent (..) directory
	# designations.
	re_baseless = re.compile(r"(^(/|\.|\.\.)|/(\.|\.\.))/*$")

	@functools.cached_property
	def local(self):
		assert isinstance(self, CmdFTP)
		return Globber()

	@functools.cached_property
	def remote(self):
		assert isinstance(self, CmdFTP)
		return VirtualGlobber(discover_remote_blobs(self))

	# Right-justify the @col:th column in @rows, or delete it.
	def rjust_column(self, rows: Sequence[list[Optional[str]]], col: int,
		  		min_width: Optional[int] = None) -> None:
		width = None
		for row in rows:
			if row[col] is not None:
				width = max(width or 0, len(row[col]))

		if width is not None and min_width is not None:
			width = max(width, min_width)

		for row in rows:
			if width is None:
				del row[col]
			elif row[col] is not None:
				row[col] = row[col].rjust(width)
			elif col < len(row) - 1:
				row[col] = ' ' * width
			else:
				del row[col]

class CmdFTP(CmdExec, CommonOptions, DownloadBlobOptions,
		DecompressionOptions, CompressionOptions,
		FTPClient):
	cmd = "ftp"
	help = "TODO"

	@functools.cached_property
	def subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdFTPDir(self), CmdFTPDu(self), CmdFTPRm(self),
			CmdFTPGet(self), CmdFTPPut(self))

	def split(self, s: str) -> Iterable[str]:
		token = None
		quoted = None
		escaped = False
		for c in s:
			if escaped:
				assert token is not None
				if c == '\\' or c in Globber.GLOBBING:
					token += rf'\{c}'
				else:
					token += c
				escaped = False
			elif quoted is not None:
				assert token is not None
				if c == quoted:
					quoted = None
				elif c == '\\':
					escaped = True
				elif c in Globber.GLOBBING:
					token += rf'\{c}'
				else:
					token += c
			elif c.isspace():
				if token is not None:
					yield token
					token = None
			else:
				if token is None:
					token = ""
				if c == '\\':
					escaped = True
				elif c in ('"', "'"):
					quoted = c
				else:
					token += c

		if escaped:
			raise ValueError("Dangling escape character")
		elif quoted is not None:
			raise ValueError("Unclosed quotation")
		elif token is not None:
			yield token

	def execute(self) -> None:
		import readline

		error = False
		re_shell = re.compile(r"^\s*!(.*)")
		while True:
			try:
				line = input("%s> " % self.remote.cwd.path())
			except KeyboardInterrupt:
				print()
				continue
			except EOFError:
				print()
				break

			if (m := re_shell.match(line)) is not None:
				ret = subprocess.run(m.group(1), shell=True)
				error = ret.returncode != 0
				continue

			try:
				cmdline = list(self.split(line))
			except ValueError as ex:
				print(f"Syntax error: {ex}", file=sys.stderr)
				error = True
				continue

			if not cmdline or cmdline[0].startswith('#'):
				continue
			if cmdline[0].startswith('-'):
				print(f"Invalid command.", file=sys.stderr)
				error = True
				continue

			try:
				error = not CmdFTPShell(self).run(cmdline)
			except SystemExit as ex:
				# argparse.parse_args() exited.
				error = ex.code != 0
			except KeyboardInterrupt:
				error = True
			except CmdFTPExit.ExitFTP:
				break

		if error:
			sys.exit(1)

class CmdFTPShell(CmdTop):
	class ArgumentParserNoUsage(CmdTop.ArgumentParser):
		def print_usage(self, *args, **kw):
			# Don't add the usage when printing an error.
			pass

	class ArgumentParser(ArgumentParserNoUsage):
		def __init__(self, *args, **kw):
			super().__init__(*args, **kw)

			# Patch argparse._SubParsersAction to omit the script
			# name from the usage, which would otherwise start with
			# "usage: prog.py @name".
			cls = self._registry_get("action", "parsers")
			class SubParsersAction(cls):
				def add_parser(self, name, *args, **kw):
					return super().add_parser(
							name, *args,
							**kw, prog=name)

			self.register("action", "parsers", SubParsersAction)

		def add_subparsers(self, *args, **kw):
			# The hack above is not desired for the subparsers
			# of the subparsers (the usage would omt the mid-level
			# subcommands).
			parent = CmdFTPShell.ArgumentParserNoUsage
			return super().add_subparsers(*args, **kw,
				 			parser_class=parent)

	# Remove the flags we don't want the @subcommands to have.
	def prune(self, subcommands: Iterable[CmdLineCommand]) -> None:
		for cmd in subcommands:
			cmd.remove_argument("--debug")
			self.prune(cmd.subcommands)

	@functools.cached_property
	def subcommands(self) -> Sequence[CmdLineCommand]:
		subcommands = (CmdFTPHelp(self), CmdFTPExit(self),
		 		CmdFTPLChDir(self), CmdFTPLPwd(self),
		 		CmdFTPChDir(self), CmdFTPPwd(self),
		 		CmdFTPDir(self), CmdFTPPDir(self),
		 		CmdFTPDu(self), CmdFTPRm(self),
		 		CmdFTPGet(self), CmdFTPPut(self))
		self.prune(subcommands)
		return subcommands

class CmdFTPHelp(CmdExec):
	cmd = "help"
	help = "TODO"

	topic: Optional[Sequence[str]]

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("topic", nargs='*')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.topic = args.topic

	def execute(self):
		if self.topic:
			# Run `<subcommands> --help'.
			self.topic.append("--help")
			self.parent.__class__(self).run(self.topic)
			return

		subcommands = [
			(", ".join(subcommand.aliases()), subcommand)
			for subcommand in self.parent.subcommands
		]
		maxwidth = max(len(title) for title, _ in subcommands)

		print("Available commands:")
		for title, cmd in subcommands:
			print(f"  * {title}: ", ' ' * (maxwidth - len(title)),
	 			cmd.help, sep="")

class CmdFTPExit(CmdExec):
	cmd = ("exit", "quit")
	help = "TODO"

	class ExitFTP(Exception): pass

	def execute(self):
		raise self.ExitFTP

class CmdFTPLChDir(CmdExec):
	cmd = "lcd"
	help = "TODO"

	dst: str

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("directory")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.dst = args.directory

	def execute(self):
		os.chdir(self.local.glob(os.path.expanduser(self.dst),
						at_least_one=True,
						at_most_one=True))

class CmdFTPLPwd(CmdExec):
	cmd = "lpwd"
	help = "TODO"

	def execute(self):
		print(os.getcwd())

class CmdFTPChDir(CmdExec):
	cmd = "cd"
	help = "TODO"

	dst: str

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("directory")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.dst = args.directory

	def execute(self: _CmdFTPChDir):
		self.remote.chdir(self.remote.glob(
					self.dst,
					at_least_one=True,
					at_most_one=True))

class CmdFTPPwd(CmdExec):
	cmd = "pwd"
	help = "TODO"

	def execute(self: _CmdFTPPwd):
		print(self.remote.cwd.path())

class CmdFTPDir(CmdExec):
	cmd = ("dir", "ls")
	help = "TODO"

	readdir: bool
	recursive: bool
	what: list[str]

	# Overridden by CmdFTPPDir.
	output: TextIO = sys.stdout

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["operation"]
		section.add_enable_flag("--directory", "-d")
		section.add_enable_flag("--recursive", "-R")

		self.sections["positional"].add_argument("what", nargs='*')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.readdir = not args.directory
		self.recursive = args.recursive
		self.what = args.what

	def print_files(self,
			files: Iterable[tuple[str, VirtualGlobber.DirEnt]]) \
			-> None:
		lines = [ ]
		nfiles = ndirs = 0
		total_size = SizeAccumulator()
		for path, dent in files:
			line = [ ]
			lines.append(line)

			if dent.obj is not None:
				created = dent.obj.gcs_blob.time_created \
						.timestamp()
				line.append(time.strftime(
						"%Y-%m-%d %H:%M:%S",
						time.localtime(created)))
			else:
				line.append(None)

			if dent.isdir():
				ndirs += 1
				line.append("<DIR>")
				line.append(None)
			else:
				nfiles += 1
				size = SizeAccumulator(dent.obj)
				total_size.add(size)

				line.append(size.blob_size(with_exact=True))
				line.append(size.file_size(with_exact=True))

			line.append(path)

		self.rjust_column(lines, 2, 14)
		self.rjust_column(lines, 1, 14 if nfiles > 0 else None)
		self.rjust_column(lines, 0)

		if nfiles + ndirs > 1:
			line = [ "total:" ]
			if ndirs > 0:
				line.append(str(ndirs))
				line.append(
					"directories" if ndirs > 1
					else "directory")
			if nfiles > 0:
				if ndirs > 0:
					line.append("and")
				line.append(str(nfiles))
				line.append("file" if nfiles == 1 else "files")
				line.append("in")
				line.append(total_size.get())
			print(*line, file=self.output)

		for line in lines:
			print(*line, file=self.output)

	def print_dir(self, path: str, dent: VirtualGlobber.DirEnt,
			divisor: bool = False, header: bool = False) -> None:
		if divisor:
			print(file=self.output)
		if header:
			print(f"{path}:", file=self.output)

		self.print_files((child.fname, child) for child in dent)
		if not self.recursive:
			return

		for child in dent:
			if not child.isdir():
				continue
			self.print_dir(os.path.join(path, child.fname), child,
					divisor=True, header=True)

	def execute(self: _CmdFTPDir) -> None:
		files, dirs = [ ], [ ]
		if self.what:
			for match in self.remote.globs(self.what):
				dent = self.remote.lookup(match)
				lst = dirs if self.readdir and dent.isdir() \
						else files
				lst.append((match, dent))
		else:
			dirs.append(('.', self.remote.cwd),)

		self.print_files(files)
		for i, (remote, dent) in enumerate(dirs):
			self.print_dir(remote, dent,
					divisor=bool(files or i > 0),
					header=bool(files or len(dirs) > 1
							or self.recursive))

class CmdFTPPDir(CmdFTPDir):
	cmd = "pdir"
	help = "TODO"

	def execute(self: _CmdFTPPDir) -> None:
		pager = subprocess.Popen(("sensible-pager",),
						stdin=subprocess.PIPE,
			   			text=True)
		self.output = pager.stdin
		super().execute()
		pager.stdin.close()
		pager.wait()

class CmdFTPDu(CmdExec):
	cmd = "du"
	help = "TODO"

	what: list[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("what", nargs='*')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.what = args.what

	def duit(self, dent: VirtualGlobber.DirEnt) \
			-> tuple[int, SizeAccumulator]:
		if dent.isdir():
			total_files = 0
			total_size = SizeAccumulator(0)
			for child in dent:
				n, size = self.duit(child)
				total_files += n
				total_size.add(size)
			return total_files, total_size
		elif dent.obj is not None:
			return (1, SizeAccumulator(dent.obj))
		else:
			return (1, SizeAccumulator())

	def execute(self: _CmdFTPDu) -> None:
		if self.what:
			lines = [ ]
			has_dirs = False
			total_files = 0
			total_size = SizeAccumulator(0)
			for match in self.remote.globs(self.what):
				dent = self.remote.lookup(match)
				has_dirs |= dent.isdir()

				n, size = self.duit(dent)
				total_files += n
				total_size.add(size)

				lines.append([
					size.blob_size(with_exact=True),
					size.file_size(with_exact=True),
					match,
				])

			# @self.what must have matched something.
			assert len(lines) > 0
			self.rjust_column(lines, 1, 10)
			self.rjust_column(lines, 0)
			for line in lines:
				print(*line)

			if total_files <= 1 and not has_dirs:
				return
		else:
			total_files, total_size = self.duit(self.remote.cwd)

		line = [ total_size.get() ]
		line.append("in")
		line.append(str(total_files))
		line.append("file" if total_files == 1 else "files")
		print(*line)

class CmdFTPRm(CmdExec):
	cmd = "rm"
	help = "TODO"

	recursive: bool
	verbose: bool
	what: list[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["operation"]
		section.add_enable_flag("--recursive", "-r", "-R")
		section.add_enable_flag("--verbose", "-v")

		self.sections["positional"].add_argument("what", nargs='+')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.recursive = args.recursive
		self.verbose = args.verbose
		self.what = args.what

	def execute(self: _CmdFTPDu) -> None:
		to_delete = [ ]
		for match in self.remote.globs(self.what):
			dent = self.remote.lookup(match)
			if not self.recursive and dent.isdir():
				raise IsADirectoryError(match)
			to_delete.append(dent)

		deleted = set()
		nfiles = size = 0
		for top in to_delete:
			for dent in top.scan():
				# A file may be included by multiple
				# @top directories.
				if dent in deleted:
					continue
				deleted.add(dent)

				if not dent.isdir():
					if self.verbose:
						print("Deleting %s..."
							% dent.path())
					size += dent.obj.gcs_blob.size
					nfiles += 1

					dent.obj.gcs_blob.delete()

			if top.isdir():
				if top is self.remote.root:
					# rm -rf /
					self.remote.cwd = top
				elif self.remote.cwd.is_parent(top):
					# @cwd is or is under @top.
					self.remote.cwd = top.parent

		if self.remote.root in deleted:
			self.remote.root.infanticide()
		else:
			for dent in deleted:
				dent.parent.remove(dent)

		if self.verbose:
			print("Deleted %d file(s) of %s."
				% (nfiles, humanize_size(size)))

class CmdFTPGet(CmdExec):
	cmd = "get"
	help = "TODO"

	src: list[str]
	dst: Optional[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()

		self.sections["positional"].add_argument("what", nargs='+')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.dst = args.what.pop() if len(args.what) > 1 else None
		self.src = args.what

	def execute(self) -> None:
		cmd_ftp_get(self)

def cmd_ftp_get(self: _CmdFTPGet) -> None:
	remote = [
		(match, self.remote.lookup(match))
		for match in self.remote.globs(self.src)
	]

	if self.dst is None:
		local = '.'
	elif not isinstance(self.parent, CmdFTPShell):
		# Globbing must have been done by the user's shell.
		local = self.dst
	else:
		local = self.local.glob(os.path.expanduser(self.dst),
						at_least_one=True,
						at_most_one=True,
						must_exist=False)
	local = pathlib.PurePath(local)

	try:
		local_isdir = stat.S_ISDIR(os.stat(local).st_mode)
	except FileNotFoundError:
		local_isdir = None

	if local_isdir is False and (len(remote) > 1 or remote[0][1].isdir()):
		raise NotADirectoryError(local)
	elif local_isdir is None and len(remote) > 1:
		raise FileNotFoundError(local)

	for src, src_top in remote:
		src_tree = src_top.scan()
		dst_top = local

		if local_isdir:
			if self.re_baseless.search(src):
				src_tree = src_top.scan(include_self=False)
			else:
				dst_top = dst_top.joinpath(src_top.fname)

		for src in src_tree:
			dst = dst_top / src.path(src_top)
			if src.isdir():
				print("MKDIR(%s)" % dst)
			else:
				print("DOWNLOAD(%s => %s)" % (src.path(), dst))

class CmdFTPPut(CmdExec):
	cmd = "put"
	help = "TODO"

	follow_symlinks: bool
	src: list[str]
	dst: Optional[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["operation"]
		section.add_enable_flag("--follow-symlinks", "--dereference",
					"-L")

		self.sections["positional"].add_argument("what", nargs='+')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.follow_symlinks = args.follow_symlinks
		self.dst = args.what.pop() if len(args.what) > 1 else None
		self.src = args.what

	def execute(self) -> None:
		cmd_ftp_put(self)

def upload_file(self: _CmdFTPPut,
		src: Union[str, os.PathLike], dst: Union[str, os.PathLike]) \
		-> int:
	with MetaBlob.create(self, str(dst)) as blob:
		pass

	print(f"Uploading {src}...", end="", flush=True)
	try:
		return upload_blob(self, blob, pipeline_stdin=open(src, "rb"))
	finally:
		print()

def cmd_ftp_put(self: _CmdFTPPut) -> None:
	if isinstance(self.parent, CmdFTPShell):
		local = self.local.globs(map(os.path.expanduser, self.src))
	else:
		local = self.src
	local = [ (src, os.stat(src).st_mode) for src in local ]

	for src, mode in local:
		if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
			raise ValueError(
				f"{src}: not a regular file or directory")

	if self.dst is not None:
		remote = self.remote.lookup(
				self.remote.glob(self.dst,
						at_least_one=True,
						at_most_one=True,
						must_exist=False),
				create=True)
	else:
		remote = self.remote.cwd

	if (len(local) > 1 or stat.S_ISDIR(local[0][1])) \
			and not remote.isdir():
		if remote.volatile:
			remote.rollback()
			raise FileNotFoundError(remote.path())
		else:
			raise NotADirectoryError(remote.path())

	seen = set() if self.follow_symlinks else None
	for src, mode in local:
		if stat.S_ISREG(mode):
			dst = remote.path()
			if remote.isdir():
				dst = dst.joinpath(os.path.basename(src))
			#print(f"UPLOAD({src} => {dst})")
			upload_file(self, src, dst)
			continue

		src_top = pathlib.PurePath(src)
		dst_top = remote.path()
		if not remote.volatile and not self.re_baseless.search(src):
			dst_top = dst_top.joinpath(src_top.name)

		for dirpath, dirs, files in os.walk(
				src_top, followlinks=self.follow_symlinks):
			dirpath = pathlib.PurePath(dirpath)
			dst_dir = dst_top / dirpath.relative_to(src_top)
			for fname in files:
				src = dirpath / fname
				if stat.S_ISREG(os.stat(src).st_mode):
					dst = dst_dir / fname
					print(f"Uploading {src}...", end="")
					#print(f"UPLOAD({src} => {dst})")
					upload_blob(self,
						MetaBlob(self, str(dst)),
						pipeline_stdin=open(src))

			# Don't descend into @dirs we've @seen.
			if seen is not None:
				sbuf = os.stat(dirpath)
				seen.add((sbuf.st_dev, sbuf.st_ino))

				i = 0
				remove = [ ]
				for dname in dirs:
					sbuf = os.stat(dirpath / dname)
					if (sbuf.st_dev, sbuf.st_ino) in seen:
						remove.append(i)
					else:
						i += 1

				for i in remove:
					del dirs[i]

class _CmdFTPChDir(CmdFTP, CmdFTPChDir): pass
class _CmdFTPPwd(CmdFTP, CmdFTPPwd): pass
class _CmdFTPDir(CmdFTP, CmdFTPDir): pass
class _CmdFTPPDir(CmdFTP, CmdFTPPDir): pass
class _CmdFTPDu(CmdFTP, CmdFTPDu): pass
class _CmdFTPRm(CmdFTP, CmdFTPRm): pass
class _CmdFTPGet(CmdFTP, CmdFTPGet): pass
class _CmdFTPPut(CmdFTP, CmdFTPPut): pass

# Non-executable subcommands {{{
class CmdList(CmdLineCommand):
	cmd = "list"
	help = "TODO"

	@functools.cached_property
	def subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdListBuckets(), CmdListLocal(), CmdListRemote())

class CmdDelete(CmdLineCommand):
	cmd = "delete"
	help = "TODO"

	@functools.cached_property
	def subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdDeleteLocal(), CmdDeleteRemote())

class CmdIndex(CmdLineCommand):
	cmd = "index"
	help = "TODO"

	@functools.cached_property
	def subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdListIndex(), CmdGetIndex(), CmdDeleteIndex())

# The top-level command.
class CmdMain(CmdTop):
	description = "TODO"

	@functools.cached_property
	def subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdList(), CmdDelete(), CmdIndex(),
	  		CmdUpload(), CmdDownload(), CmdFTP())
# }}}

# Main starts here. {{{
main = CmdMain()
try:
	sys.exit(not main.run())
except KeyboardInterrupt:
	if not main.debug:
		sys.exit(1)
	raise
# }}}

# vim: set foldmethod=marker:
# End of giccs.py
