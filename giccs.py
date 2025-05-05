#!/home/adam/prog/src/gcs/volatile/venv/bin/python3

# Modules {{{
from __future__ import annotations

from typing import	TypeVar, ParamSpec, Protocol, Self, \
			Any, Union, Optional, Final, \
			Generator, Iterator, Iterable, Callable, \
			Container, Collection, Sequence, \
			TextIO, BinaryIO, ByteString

import sys, os, errno
import io, fcntl, stat
import subprocess, multiprocessing
import pathlib, glob2
import time, datetime
import re, bisect, uuid
import base64, binascii
import random, secrets
import hashlib, hmac
import argparse, configparser, shlex
import enum, dataclasses, struct
import contextlib, functools

import btrfs

import google.cloud.storage
import google.cloud.storage_control_v2
import google.cloud.storage_control_v2.types
import google.oauth2.service_account
from google.api_core.exceptions import GoogleAPICallError
# }}}

# Constants and structures {{{
# A generic-purpose type variable.
T = TypeVar("T")

# Cached singletons.
UUID0 = uuid.UUID(int=0)

CurDir = pathlib.PurePath('.')
RootDir = pathlib.PurePath('/')

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

FICLONE = btrfs.ioctl._IOW(0x94, 9, struct.Struct("@i"))
# }}}

# Exceptions {{{
class GiCCSError(Exception):
	# Dig the detailed error message out of GoogleAPICallError.
	def parse_GoogleAPICallError(self, ex: GoogleAPICallError) -> str:
		error = [ ex.code.name ]
		if ex.response is None:
			return error[0]

		import grpc
		from requests.exceptions import JSONDecodeError

		if isinstance(ex.response, grpc.Call):
			return ex.response.details()

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

	def __str__(self):
		args = self.args
		if not args and self.__cause__ is not None:
			args = (self.__cause__,)

		parts = [ ]
		for arg in args:
			if isinstance(arg, GoogleAPICallError):
				parts.append(
					self.parse_GoogleAPICallError(arg))
			else:
				parts.append(str(arg))

		args = ' '.join(parts)
		if isinstance(self.__cause__, OSError) \
				and self.__cause__.errno is None:
			if isinstance(self.__cause__, FileExistsError):
				self.__cause__.errno = errno.EEXIST
			elif isinstance(self.__cause__, FileNotFoundError):
				self.__cause__.errno = errno.ENOENT
			elif isinstance(self.__cause__, IsADirectoryError):
				self.__cause__.errno = errno.EISDIR
			elif isinstance(self.__cause__, NotADirectoryError):
				self.__cause__.errno = errno.ENOTDIR

			if self.__cause__.errno is not None:
				return "[Errno %d] %s: %s" % (
					self.__cause__.errno,
					os.strerror(self.__cause__.errno),
					args)

		return args

# Bad user input.
class UserError(GiCCSError): pass

# Any other non-recoverable error.
class FatalError(GiCCSError): pass

# Possible foul-play detected.
class SecurityError(FatalError): pass

# System is in an unexpected state.
class ConsistencyError(FatalError): pass
# }}}

# Command line parsing {{{
# A mixin making it easier to convert between choices made in the config file
# and enum values.
class Choices: # {{{
	@classmethod
	def to_choices(self):
		return tuple(v.name.lower().replace('_', '-') for v in self)

	@classmethod
	def from_choice(self, choice: str):
		return self.__getitem__(choice.replace('-', '_').upper())
# }}}

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
		Option: TypeAlias = tuple[Sequence[str], dict[str, Any]]
		options: list[Union[Option, Mutex]]

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

		# Called by CmdLineOptions.find_argument().
		def find_argument(self, flag: str) -> Optional[Option]:
			for i, option in enumerate(self.options):
				if isinstance(option, CmdLineOptions.Mutex):
					found = option.find_argument(flag)
					if found is not None:
						return found
				elif flag in option[0]:
					return option
			return None

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
			("deletion",	"Deletion options"		),
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
			tpe: Union[type[bool], type[int], type[str],
					Container[str]] = str) -> None:
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
				elif tpe is not str and val not in tpe:
					raise self.CmdLineError(
						"%s must be one of %s"
						% (key, ", ".join(tpe)))
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
		what = what.replace('_', '-')
		try:
			lst = shlex.split(s)
		except ValueError as ex:
			raise self.CmdLineError(f"{what}: {ex}") from ex

		if not lst and not empty_ok:
			raise self.CmdLineError(f"{what}: missing value")
		return lst

	# Is stdin a terminal?
	@functools.cached_property
	def interactive(self) -> bool:
		return os.isatty(sys.stdin.fileno())

	# Public methods.
	# Find the declaration of an argument.
	def find_argument(self, flag: str) -> Optional[Section.Option]:
		for section in self.sections.values():
			found = section.find_argument(flag)
			if found is not None:
				return found
		return None

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
		self.parent = parent
		super().__init__()

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

		if self.parent is None:
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

	@classmethod
	@property
	@functools.cache
	def debug(self) -> bool:
		debug = os.environ.get("GICCS_DEBUG")
		if debug is None:
			return False

		try:
			return int(debug) > 0
		except ValueError:
			return debug.lower() in ("true", "yes", "on")

	@classmethod
	def print_exception(cls):
		if cls.debug:
			# Print the backtrace when debugging.
			import traceback
			traceback.print_exc()
		else:
			ex = sys.exception()
			print("%s: %s" % (type(ex).__name__, ex),
				file=sys.stderr)

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
				Globber.MatchError,
				FileNotFoundError, FileExistsError,
				NotADirectoryError, IsADirectoryError):
			self.print_exception()
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
				cmd.terminate()
			raise self.CmdLineError(f"{src}: {ex}") from ex
		else:
			if not isinstance(self.service_account_info, dict):
				raise self.CmdLineError(f"{src}: not a dict")
		finally:
			if cmd is not None:
				wait_proc(cmd)

	@functools.cached_property
	def creds(self) -> Optional[google.oauth2.service_account.Credentials]:
		if self.service_account_info is None:
			return None

		return google.oauth2.service_account.Credentials. \
				from_service_account_info(
					self.service_account_info)

	@functools.cached_property
	def gcs_client(self) -> google.cloud.storage.Client:
		return google.cloud.storage.Client(credentials=self.creds)

	@functools.cached_property
	def gcs_ctrl(self) -> google.cloud.storage_control_v2. \
				StorageControlClient:
		return google.cloud.storage_control_v2.StorageControlClient(
				credentials=self.creds)
# }}}

# Provide options to specify the GCS bucket to use.
class BucketOptions(AccountOptions): # {{{
	# Can be overridden by subclasses.
	bucket_required: bool = False

	bucket_name:	Optional[str] = None
	bucket_labels:	Optional[dict[str, Optional[str]]] = None
	prefix:		pathlib.PurePath = CurDir

	def declare_arguments(self) -> None:
		super().declare_arguments()

		# We can't mark the @mutex required because the options
		# may be provided through the config file.
		section = self.sections["bucket"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_argument("--bucket", "-b")
		mutex.add_argument("--bucket-labels", "-B", action="append")
		section.add_argument("--prefix", "-p")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		if not isinstance(self, CmdListBuckets):
			# Ignore the settings in the config for the
			# "list buckets" command.
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

		# Transform a list of LABEL=VALUE items into a dictionary.
		if bucket_labels is not None:
			self.bucket_labels = { }
			for label in bucket_labels:
				key, eq, val = label.partition('=')
				self.bucket_labels[key] = val if eq else None

		self.merge_options_from_ini(args, "prefix")
		if args.prefix is not None:
			self.prefix = pathlib.PurePath(args.prefix)
			if ".." in self.prefix.parts:
				raise self.CmdLineError(
						"--prefix must not "
						"contain \"..\"")
			if self.prefix.is_absolute():
				self.prefix = prefix.relative_to(RootDir)

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
			bucket = self.gcs_client.bucket(self.bucket_name)
			try:
				if not bucket.exists():
					raise UserError(
						f"{self.bucket_name}: "
						"no such bucket")
			except GoogleAPICallError as ex:
				raise FatalError(
					f"{self.bucket_name}:", ex) from ex
			return bucket

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

	# Returns whether @self.bucket has hierarchical namespace enabled.
	@functools.cached_property
	def is_hfs(self) -> bool:
		storage_layout_path = self.gcs_ctrl.storage_layout_path(
					"_", self.bucket.name)
		storage_layout = self.gcs_ctrl.get_storage_layout(
					name=storage_layout_path)
		return storage_layout.hierarchical_namespace.enabled

	# Return the bucket name or "<bucket-name>/<prefix>".
	def bucket_with_prefix(self) -> str:
		return str(self.bucket.name / self.prefix)

	# Return a GCS prefix that matches all blobs under @path.
	def with_prefix(self, path: pathlib.PurePath | str) -> Optional[str]:
		if isinstance(path, pathlib.PurePath) and path.is_absolute():
			path = path.relative_to(RootDir)
		path = self.prefix / path
		return f"{path}/" if path.parts else None

	# Strip @self.prefix from @path if it's defined.
	def without_prefix(self, path: str) -> str:
		if self.prefix.parts:
			prefix = f"{self.prefix}/"
			if not path.startswith(prefix):
				raise ConsistencyError(
					f"{path} doesn't start with {prefix}")
			return path.removeprefix(prefix)
		else:
			return path

	def bucket_path(self) -> str:
		return "%s/buckets/%s" % (
				self.gcs_ctrl.common_project_path('_'),
				self.bucket.name)

	def folder_path(self, folder_id: str) -> str:
		return self.gcs_ctrl.folder_path('_',
				self.bucket.name, folder_id)

	# @folder_id is "dir/subdir/" (it must end with a '/')
	def create_folder(self, folder_id: str) -> None:
		if not self.is_hfs:
			return

		req = google.cloud.storage_control_v2.types. \
					CreateFolderRequest(
						parent=self.bucket_path(),
						folder_id=folder_id,
						recursive=True)
		try:
			self.gcs_ctrl.create_folder(request=req)
		except GoogleAPICallError as ex:
			raise FatalError from ex

	def delete_folder(self, folder_id: str) -> None:
		if not self.is_hfs:
			return

		try:
			self.gcs_ctrl.delete_folder(
				name=self.folder_path(folder_id))
		except GoogleAPICallError as ex:
			raise FatalError from ex

	def rename_folder(self, src_folder_id: str, dst_folder_id: str) \
				-> None:
		# This is a requirement because this is not a nice-to-have
		# operation which we can skip silently.
		assert self.is_hfs

		self.gcs_ctrl.rename_folder(
			name=self.folder_path(src_folder_id),
			destination_folder_id=dst_folder_id)
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

# Add --wet-run.
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
					f"--{flag} {val}: {ex}") from ex

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
	volume:			Optional[str] = None

	meta_cipher:		Optional[InternalCipher.Primitive] = None
	bulk_cipher:		Optional[InternalCipher.Primitive] = None

	encryption_key:		Optional[bytes] = None
	encryption_key_command:	Optional[Sequence[str]] = None

	encryption_command:	Optional[Sequence[str]] = None
	decryption_command:	Optional[Sequence[str]] = None

	random_blob_uuid:	bool = False
	encrypt_metadata:	bool = False
	add_header_to_blob:	bool = False

	padding: Optiona[Progressometer.Padding] = None

	class Integrity(Choices, enum.IntEnum):
		NONE		= enum.auto()
		SIZE		= enum.auto()
		HASH		= enum.auto()
	integrity: Integrity = Integrity.NONE

	def encrypt_internal(self) -> bool:
		return bool(self.meta_cipher or self.bulk_cipher)

	def encrypt_external(self) -> bool:
		return bool(self.encryption_command or self.decryption_command)

	@property
	def encrypt(self):
		return self.encrypt_internal() or self.encrypt_external()

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["bucket"]
		section.add_argument("--volume", "-V")

		section = self.sections["encryption"]
		section.add_argument("--meta-cipher")
		section.add_argument("--bulk-cipher", "--cipher")
		section.add_argument("--encryption-command", "--encrypt")
		section.add_argument("--decryption-command", "--decrypt")
		mutex = section.add_mutually_exclusive_group()
		mutex.add_argument("--encryption-key", "--key")
		mutex.add_argument("--encryption-key-command", "--key-cmd")

		section.add_enable_flag_no_dflt("--random-blob-uuid")
		section.add_disable_flag_no_dflt("--no-encrypt-metadata")
		section.add_disable_flag_no_dflt("--no-blob-header")

		choices = [ "none" ]
		choices += Progressometer.Padding.to_choices()
		section.add_argument("--padding", choices=choices)

		choices = self.Integrity.to_choices()
		section.add_argument("--integrity", choices=choices)

	def resolve_internal_cipher(self, which: str, *names: str) \
					-> InternalCipher.Primitive:
		for name in names:
			cipher = InternalCipher.look_up_cipher(name)
			if cipher is not None:
				return cipher

		if len(names) > 1:
			msg = f"couldn't find a suitable {which}"
		else:
			msg = f"invalid {which}"
		ciphers = ", ".join(
				cipher.__name__ for cipher
				in InternalCipher.available_ciphers())
		raise self.CmdLineError(f"{msg}, choose from {ciphers}")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args, "volume")
		self.volume = args.volume

		self.merge_options_from_ini(args,
			("encryption_command", "decryption_command"),
			("meta_cipher", "bulk_cipher"))
		self.merge_options_from_ini(args,
			"encryption_key", "encryption_key_command")

		if args.meta_cipher is not None:
			self.meta_cipher = self.resolve_internal_cipher(
							"meta-cipher",
							args.meta_cipher)
		if args.bulk_cipher is not None:
			self.bulk_cipher = self.resolve_internal_cipher(
							"bulk-cipher",
							args.bulk_cipher)

		if args.encryption_command is not None:
			self.encryption_command = \
				self.shlex_split(
					"encryption-command",
					args.encryption_command)
		if args.decryption_command is not None:
			self.decryption_command = \
				self.shlex_split(
					"decryption-command",
					args.decryption_command)
		if (self.encryption_command is not None) \
				!= (self.decryption_command is not None):
			raise self.CmdLineError(
					"encryption-command "
					"and decryption-command "
					"must be specified together")
		assert not (self.encrypt_internal() \
				and self.encrypt_external())

		if args.encryption_key is not None:
			has_key = True
			try:
				self.encryption_key = base64.b64decode(
						args.encryption_key,
						validate=True)
			except binascii.Error as ex:
				raise self.CmdLineError(
					"encryption-key is not a valid "
					"base-64 string") from ex
		elif args.encryption_key_command is not None:
			has_key = True
			self.encryption_key_command = \
				self.shlex_split(
					"encryption-key-command",
					args.encryption_key_command)
		else:
			has_key = False

		if self.encrypt_internal() and not has_key:
			raise self.CmdLineError(
					"either encryption-key "
					"or encryption-key-command "
					"must be specified")

		if has_key and not self.encrypt_external():
			# Choose safe defaults.
			if self.meta_cipher is None:
				self.meta_cipher = \
					self.resolve_internal_cipher(
							"meta-cipher",
							"AESGCMSIV", "AESSIV")
			if self.bulk_cipher is None:
				self.bulk_cipher = self.meta_cipher

		self.merge_options_from_ini(args, "random_blob_uuid", tpe=bool)
		if args.random_blob_uuid:
			self.random_blob_uuid = True

		self.merge_options_from_ini(args, "encrypt_metadata", tpe=bool)
		if args.encrypt_metadata is not False:
			self.encrypt_metadata = self.encrypt

		if self.encrypt_external() and self.encrypt_metadata \
				and has_key:
			# We'd only use encryption-key to sign the metadata.
			# Encryption is performed through encryption-command.
			raise self.CmdLineError(
					"encryption-key won't be used "
					"with encrypt-metadata")

		self.merge_options_from_ini(args, "blob_header", tpe=bool)
		if args.blob_header is not False:
			self.add_header_to_blob = self.encrypt
		elif not self.encrypt_external():
			# InternalEncrypt always writes a header.
			raise self.CmdLineError(
				"--no-blob-header only makes sense with "
				"--encryption-command/--decryption-command")

		# It makes some sense to enable padding even if encryption
		# (at rest) is not enabled, because it makes the analysis
		# of traffic in transit (which is still encrypted) harder
		# by outsiders.  But this is probably not something the user
		# would expect by default.
		choices = self.find_argument("--padding")[1]["choices"]
		self.merge_options_from_ini(args, "padding", tpe=choices)
		if args.padding is None:
			# Since the amount of padding will be stored with the
			# metadata, it needs to be encrypted.
			if self.encrypt_metadata:
				# The Covert-scheme seems to be more secure
				# and efficient than Padme as long as the user
				# doesn't upload the same file multiple times.
				self.padding = Progressometer.Padding.COVERT
		elif args.padding != "none":
			self.padding = Progressometer.Padding.from_choice(
								args.padding)

		# Integrity-protection requires an extra permission because
		# it needs to update the blob's metadata after its creation.
		choices = self.find_argument("--integrity")[1]["choices"]
		self.merge_options_from_ini(args, "integrity", tpe=choices)
		if args.integrity is not None:
			self.integrity = self.Integrity.from_choice(
							args.integrity)
		elif self.encrypt:
			self.integrity = self.Integrity.HASH
		if self.integrity != self.Integrity.NONE and not self.encrypt:
			raise self.CmdLineError(
				"integrity-protection requires encryption")

class EncryptedBucketOptions(EncryptionOptions, BucketOptions):
	# Initialize @self.volume if it hasn't been set explicitly.
	@property
	def bucket(self) -> google.cloud.storage.Bucket:
		bucket = super().bucket

		if self.volume is None:
			self.volume = str(pathlib.PurePath(bucket.name)
						/ self.prefix)

		return bucket

	def create_folder(self, folder_id: str) -> None:
		if not self.encrypt_metadata:
			super().create_folder(folder_id)

	def delete_folder(self, folder_id: str) -> None:
		if not self.encrypt_metadata:
			super().delete_folder(folder_id)
# }}}

# Add --upload-chunk-size, --progress and --timeout.
class TransferOptions(CmdLineOptions): # {{{
	upload_chunk_size:	Optional[int] = None
	progress:		Optional[int] = None
	timeout:		Optional[int] = None
	laggy:			bool = False

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["transfer"]
		if isinstance(self, (CmdUpload, CmdFTP)):
			section.add_int_argument("--upload-chunk-size")
		section.add_int_argument("--progress")
		section.add_int_argument("--timeout")
		section.add_enable_flag_no_dflt("--laggy")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		if isinstance(self, (CmdUpload, CmdFTP)):
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

		self.merge_options_from_ini(args, "laggy", tpe=bool)
		if args.laggy:
			self.laggy = args.laggy

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
				% (blob.blob_name, blob.snapshot_name,
					self.snapshot_name))
		elif blob.snapshot_uuid != self.snapshot_uuid:
			raise ConsistencyError(
				"%s has unexpected snapshot UUID "
				"(%s != %s)"
				% (blob.blob_name, blob.snapshot_uuid,
					self.snapshot_uuid))

		existing = getattr(self, blob.payload_type.field())
		if existing is not None:
			raise ConsistencyError(
				"%s has duplicate %s blobs (%s and %s)"
				% (self, blob.payload_type.field(),
					existing.blob_name, blob.blob_name))

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

# A cryptographycally-secure deterministic random number generator based on
# AES-CTR.
class CSPRNG: #  {{{
	# The cipher we'll obtain the random bytes from by feeding it zeroes.
	class Primitive(Protocol):
		def update_into(data: ByteString, buf: ByteString) -> int:
			...
	generator: Primitive

	# The key of the cipher, either supplied by the user or generated
	# randomly.  Two CSPRNG:s seeded with the same value should produce
	# the same byte sequence.
	seed: bytes

	# The size of the seed to generate by default.
	DFLT_SEED_SIZE: int = 128 // 8

	# The number of random bytes we'll generate at a time.  The cipher
	# has been measured to be the fasted with this input size.
	MAXBUF: int = 128*1024

	# The input of the cipher, MAXBUF number of zero bytes.
	zeroes: memoryview

	# How much the output buffer needs to be larger than the input.
	SURPLUS: int

	# The output buffer filled by the cipher.  Its size is not a multiply
	# of MAXBUF.
	buf: bytearray

	# The number of bytes that have been returned from the output buffer.
	buf_i: int

	# Points at the first unfilled byte in the output buffer.
	buf_n: int

	def __init__(self, seed: Optional[bytes] = None):
		# We import the library on-demand.
		from cryptography.hazmat.primitives.ciphers \
			import Cipher, algorithms, modes

		if seed is None:
			# Use AES-128 by default.
			seed = secrets.token_bytes(self.DFLT_SEED_SIZE)
		else:
			assert len(seed) >= self.DFLT_SEED_SIZE
		algo = algorithms.AES(seed)
		self.seed = seed

		# The nonce is also a sequence of zeroes.  This is OK,
		# since the key is not supposed to be reused.
		block_size = algo.block_size // 8
		mode = modes.CTR(bytes(block_size))
		self.SURPLUS = block_size - 1

		self.generator = Cipher(algo, mode).encryptor()
		self.zeroes = memoryview(bytes(self.MAXBUF))

		self.buf = bytearray()
		self.buf_i = self.buf_n = 0

	# Return @n random bytes.
	def generate(self, n: int) -> memoryview:
		# Can we readily return @n bytes from the output buffer?
		if n <= self.buf_n - self.buf_i:
			i = self.buf_i
			self.buf_i += n
			return memoryview(self.buf)[i:i+n]

		# We need to enlarge the buffer by an integer times of MAXBUF,
		# such that we'll have enough output to return @n bytes.
		# We can ignore the already returned portion of the buffer
		# (everything up to @self.buf_i).
		#
		#                                .MAXBUF.MAXBUF.MAXBUF.MAXBUF.
		# |........|.....................|......|......|......|..+...|
		# buf      buf_i                 buf_n                   |
		#          `------------------------+--------------------'
		#                                   n  
		#
		# @newbuf is how much more to allocate.  It's slightly more
		# than necessary because in theory the cipher could return
		# SURPLUS more bytes for every MAXBUF input.
		q, r = divmod(n - (self.buf_n - self.buf_i), self.MAXBUF)
		newbuf = (q + (r > 0)) * (self.MAXBUF + self.SURPLUS)

		assert self.buf_i <= self.buf_n
		self.buf_n -= self.buf_i

		# Allocate the new buffer and copy the unreturned bytes from
		# @oldbuf.  This is faster than trimming and extending the
		# buffer.
		oldbuf = memoryview(self.buf)
		self.buf = bytearray(self.buf_n + newbuf)
		self.buf[:self.buf_n] = \
			oldbuf[self.buf_i:self.buf_i+self.buf_n]

		# Fill in the rest of the buffer, MAXBUF at a time.
		view = memoryview(self.buf)
		while self.buf_n < n:
			self.buf_n += self.generator.update_into(
					self.zeroes, view[self.buf_n:])

		# Return the requested number of bytes.
		self.buf_i = n
		return view[:n]

	# Check whether @rnd matches what is coming up in the sequence.
	# If so, returns None, otherwise the offset of the first difference.
	# This is more efficient than generate()ing the sequence and comparing
	# it with @rnd.
	def verify(self, rnd: ByteString) -> Optional[int]:
		# Run until @rnd is consumed.
		n, i = len(rnd), 0
		rnd = memoryview(rnd)
		while n > 0:
			# Are there any bytes remaining in the buffer?
			if self.buf_i >= self.buf_n:
				# No, let's generate the next batch.
				self.buf = bytearray(self.MAXBUF+self.SURPLUS)
				self.buf_n = self.generator.update_into(
							self.zeroes, self.buf)
				self.buf_i = 0

			# Compare the next @cmp bytes.  For some reason
			# comparing two memoryview:s is very slow, so we
			# use @self.buf as-is.
			cmp = min(n, self.buf_n - self.buf_i)
			if self.buf[self.buf_i:self.buf_i+cmp] != rnd[i:i+cmp]:
				# Find the first differing offset.
				while True:
					assert i < cmp
					if self.buf[self.buf_i] != rnd[i]:
						return i
					i += 1
					self.buf_i += 1

			i += cmp
			n -= cmp
			self.buf_i += cmp

		assert n == 0
		return None
# }}}

# The internal encryption and decryption classes.
class InternalCipher: # {{{
	# The cryptography.hazmat.primitives.ciphers.aead module,
	# imported dynamically, only when necessary.
	aead: types.ModuleType

	# The interface of the various ciphers in the aead module. {{{
	class PrimitiveBase(Protocol):
		def __init__(self, key: bytes):
			...

		def generate_key(self, bits: int) -> bytes:
			...

	class PrimitiveCommon(PrimitiveBase):
		def encrypt(self, nonce: ByteString, data: ByteString,
				associated_data: Optional[ByteString]) \
				-> bytes:
			...

		def decrypt(self, nonce: ByteString, data: ByteString,
				associated_data: Optional[ByteString]) \
				-> bytes:
			...

	class PrimitiveAESSIV(PrimitiveBase):
		def encrypt(self, data: ByteString,
				associated_data: Optional[list[ByteString]]) \
				-> bytes:
			...

		def decrypt(self, data: ByteString,
				associated_data: Optional[list[ByteString]]) \
				-> bytes:
			...

	Primitive = Union[PrimitiveCommon, PrimitiveAESSIV]
	# }}}

	# Output stream structure: {{{
	# * init block:
	#   * nonce:
	#     * timestamp (4 B)
	#     * true random (8 B)
	#   * data (encrypted with the @meta_cipher):
	#     * bulk key (bulk_key_size())
	#     * prng seed (NONCE_SEED_BITS)
	#   * verification tag (AUTH_TAG_SIZE)
	# * first chunk (encrypted with the @bulk_cipher):
	#   * bulk data (CLEARTEXT_SIZE - init_block_size())
	#   * verification tag (AUTH_TAG_SIZE)
	# * next chunk:
	#   * bulk data (CLEARTEXT_SIZE)
	#   * verification tag (AUTH_TAG_SIZE)
	# [...]
	# * last chunk of the stripe:
	#   * next bulk key (bulk_key_size())
	#   * bulk data (CLEARTEXT_SIZE - bulk_key_size())
	#   * verification tag (AUTH_TAG_SIZE)
	#
	# The additional authenticated data are the @blob_uuid and
	# @data_type_id, but they are not included in the ciphertext.
	#
	# Except for the init block, the first 8 bytes of the nonce
	# is the chunk's sequence number, concatenated with a PRNG,
	# which is not included in the ciphertext.  This is to protect
	# against the ill chance of generating the same @blob_uuid for
	# multiple blobs, which would allow swapping chunks between blobs.
	# }}}

	# Tunable security parameters.
	NONCE_SIZE: Final[int]		= 12
	NONCE_SEED_BITS: Final[int]	= 64
	BULK_KEY_BITS: Final[int]	= 256

	# This is non-tunable.
	AUTH_TAG_SIZE: Final[int]	= 16

	# The various aead primitives have been measured to be the fastest
	# with this chunk size.
	CIPHERTEXT_SIZE: Final[int]	= 512 * 1024
	CLEARTEXT_SIZE: Final[int]	= CIPHERTEXT_SIZE - AUTH_TAG_SIZE

	# The maximum number of chunks to encrypt with the same @bulk_cipher.
	# A chunk is produced by one invocation of the Primitive's encrypt()
	# operation.
	CHUNKS_PER_STRIPE: Final[int]	= 1024*1024*1024 // CIPHERTEXT_SIZE

	# The init block is encrypted with the @meta_cipher, everything else
	# is encrypted with a @bulk_cipher.  The @bulk_cipher is initialized
	# when the init block is encrypted or decrypted.
	meta_cipher:			Primitive
	bulk_cipher_class:		type[Primitive]
	bulk_cipher:			Optional[Primitive]

	# @nonce_prng is initialized from the init block.  @chunk_counter
	# counts how many chunks have been encrypted or decrypted.
	nonce_prng:			Optional[random.Random]
	chunk_counter:			int

	# The additional authenticated data (@blob_uuid and @data_type_id
	# concatenated).
	auth_data:			bytearray
	blob_uuid:			uuid.UUID
	data_type_id:			int

	# The file where cleartext is read from or written to.
	wrapped:			Optional[BinaryIO]
	bytes_in:			int
	bytes_out:			int

	# Have we encountered an exception?
	borked:				Optional[Exception]

	# See if a cipher with @name is defined in the aead module.
	@classmethod
	def look_up_cipher(cls, name: str) -> Optional[Primitive]:
		from cryptography.hazmat.primitives.ciphers import aead

		cipher = getattr(aead, name, None)
		if cipher is None or type(cipher) is not type \
				or not hasattr(cipher, "encrypt"):
			return None
		return cipher

	# Return the list of ciphers defined in the aead module.
	@classmethod
	def available_ciphers(cls) -> Iterable[Primitive]:
		from cryptography.hazmat.primitives.ciphers import aead

		for sym in dir(aead):
			cipher = cls.look_up_cipher(sym)
			if cipher is not None:
				yield cipher

	# Override @self.CIPHERTEXT_SIZE and @self.CHUNKS_PER_STRIPE
	# for testing.
	@classmethod
	def override_chunk_and_stripe_size(cls,
			chunk_size: Optional[int],
			chunks_per_stripe: Optional[int]) -> None:
		if chunk_size is not None:
			cls.CIPHERTEXT_SIZE = chunk_size
			cls.CLEARTEXT_SIZE = cls.CIPHERTEXT_SIZE \
						- cls.AUTH_TAG_SIZE
		if chunks_per_stripe is not None:
			cls.CHUNKS_PER_STRIPE = chunks_per_stripe

	def __init__(self,
			meta_cipher: Primitive,
			bulk_cipher_class: type[Primitive],
			blob_uuid: uuid.UUID, data_type_id: int,
			wrapped: Optional[BinaryIO] = None):
		from cryptography.hazmat.primitives.ciphers import aead
		self.aead = aead

		self.meta_cipher = meta_cipher
		self.bulk_cipher_class = bulk_cipher_class
		self.reset(blob_uuid, data_type_id)
		self.wrapped = wrapped

	# Allows setting @self.wrapped after the object has been created.
	def init(self, wrapped: Optional[BinaryIO]) -> None:
		assert self.wrapped is None
		self.wrapped = wrapped

	# Makes the object ready to encrypt or decrypt another file.
	# Also the @blob_uuid and/or the data_type_id can be updated.
	def reset(self, blob_uuid: Optional[uuid.UUID] = None,
			data_type_id: Optional[int] = None,
			wrapped: Optional[BinaryIO] = None) -> None:
		self.bulk_cipher = None

		# Reset @self.auth_data if a new @blob_uuid or @data_type_id
		# has been set.
		if blob_uuid is not None:
			self.blob_uuid = blob_uuid
		if data_type_id is not None:
			self.data_type_id = data_type_id
		if blob_uuid is not None or data_type_id is not None:
			self.auth_data = bytearray(self.blob_uuid.bytes)
			self.auth_data += self.data_type_id.to_bytes(4)

		self.nonce_prng = None
		self.chunk_counter = 0

		if wrapped is not None:
			self.wrapped = wrapped
		self.bytes_in = self.bytes_out = 0

		self.borked = None

	# How large a key @self.bulk_cipher_class needs (in bytes) to achieve
	# BULK_KEY_BITS-level security.
	def bulk_key_size(self) -> int:
		key_size = self.BULK_KEY_BITS // 8
		if issubclass(self.bulk_cipher_class, self.aead.AESSIV):
			# SIV-AES needs two keys.
			key_size *= 2
		return key_size

	# The size of the init block, considering the bulk_key_size().
	def init_block_size(self) -> int:
		return self.NONCE_SIZE \
			+ self.bulk_key_size() \
			+ self.NONCE_SEED_BITS // 8 \
			+ self.AUTH_TAG_SIZE

	# Initialize @self.nonce_prng with a fixed version of the PRNG,
	# which is guaranteed to produce the same sequence regardless
	# of the Python version.
	def init_prng(self, seed: int) -> None:
		assert self.nonce_prng is None
		self.nonce_prng = random.Random()
		self.nonce_prng.seed(seed, version=2)

	# Generate a nonce for the next chunk.
	def next_bulk_nonce(self) -> bytearray:
		assert self.nonce_prng is not None

		nonce = bytearray(self.chunk_counter.to_bytes(8))
		nonce += self.nonce_prng.randbytes(
				self.NONCE_SIZE - len(nonce))
		self.chunk_counter += 1

		return nonce

	# If @fun is not exception-safe, but it raises one, save and re-raise
	# it in case GCS is retrying.
	T = TypeVar('T')
	P = ParamSpec('P')
	def noretry(fun: Callable[P, T]) -> Callable[P, T]:
		def wrapper(self, *args: P.args, **kwargs: P.kwargs) -> T:
			if self.borked is not None:
				raise self.borked

			try:
				return fun(self, *args, **kwargs)
			except Exception as ex:
				self.borked = ex
				raise
		return wrapper

class InternalEncrypt(InternalCipher):
	# The CSRNG to use when one is not provided to the constructor.
	class CSRNG(random.Random):
		def getrandbits(self, n: int) -> int:
			return secrets.randbits(n)

		def randbytes(self, n: int) -> bytes:
			return secrets.token_bytes(n)

	# Used to initialize @self.nonce_prng.
	csrng: random.Random

	# The output buffer.
	ciphertext: bytearray
	ciphertext_i: int

	# Has @self.wrapped been read fully?
	eof: bool

	# The @csrng can be overridden for testing.
	def __init__(self,
			meta_cipher: Primitive,
			bulk_cipher_class: type[Primitive],
			blob_uuid: uuid.UUID, data_type_id: int,
			csrng: Optional[random.Random] = None,
			wrapped: Optional[BinaryIO] = None):
		super().__init__(meta_cipher, bulk_cipher_class,
					blob_uuid, data_type_id, wrapped)
		self.csrng = csrng or self.CSRNG()

	# Also called by super().__init__().
	def reset(self, blob_uuid: Optional[uuid.UUID] = None,
			data_type_id: Optional[int] = None,
			wrapped: Optional[BinaryIO] = None) -> None:
		super().reset(blob_uuid, data_type_id, wrapped)

		self.ciphertext = bytearray()
		self.ciphertext_i = 0

		self.eof = False

	# Abstraction to invoke the @cipher's encryption function.
	def encrypt_base(self, cipher: Primitive, nonce: ByteString,
				cleartext: ByteString) -> bytes:
		if isinstance(cipher, self.aead.AESSIV):
			ciphertext = cipher.encrypt(cleartext,
						[ self.auth_data, nonce ])
		else:
			ciphertext = cipher.encrypt(nonce, cleartext,
						self.auth_data)

		self.bytes_out += len(ciphertext)
		return ciphertext

	# Encrypt the @cleartext with the @self.meta_cipher.
	def encrypt_meta(self, cleartext: ByteString) -> bytes:
		# Normally time.time() increases monotonically, ensuring the
		# uniqueness of the @nonce in most circumstances.  We also add
		# considerable entropy to make it a guarantee.
		nonce = bytearray((int(time.time()) & 0xFFFFFFFF).to_bytes(4))
		nonce += self.csrng.randbytes(self.NONCE_SIZE - len(nonce))

		ciphertext = self.encrypt_base(self.meta_cipher, nonce,
						cleartext)
		self.bytes_out += len(nonce)

		return nonce + ciphertext

	# Generate a key for @self.bulk_cipher_class.
	def gen_bulk_key(self) -> bytes:
		if not isinstance(self.csrng, self.CSRNG):
			# An external csrng was provided to __init__(),
			# so let's not use the cipher's own method, which
			# probably pulls from another random source.
			return self.csrng.randbytes(self.bulk_key_size())

		return self.bulk_cipher_class.generate_key(
						self.bulk_key_size() * 8)

	# Return at most @n bytes of ciphertext derived from data read from
	# @self.wrapped.  If @n is None, encrypt all the remaining cleartext
	# from @self.wrapped.  This function is not exception-safe, eg. we
	# don't save the cleartext read from @self.wrapped.
	@InternalCipher.noretry
	def read(self, n: Optional[int] = None) \
			-> Union[memoryview, bytearray]:
		assert self.wrapped is not None

		# Add the init block to @self.ciphertext if this is the
		# first chunk and we haven't added it yet.
		if self.bulk_cipher is None:
			assert not self.bytes_out
			assert not self.chunk_counter

			bulk_key = self.gen_bulk_key()
			self.bulk_cipher = self.bulk_cipher_class(bulk_key)

			nonce_seed = self.csrng.getrandbits(
						self.NONCE_SEED_BITS)
			self.init_prng(nonce_seed)
			nonce_seed = nonce_seed.to_bytes(
					self.NONCE_SEED_BITS // 8)

			assert not self.ciphertext
			self.ciphertext += self.encrypt_meta(
						bulk_key + nonce_seed)
			assert len(self.ciphertext) == self.init_block_size()

		# If we have enough data accumulated in @self.ciphertext,
		# return them.
		assert len(self.ciphertext) >= self.ciphertext_i
		ciphertext_len = len(self.ciphertext) - self.ciphertext_i
		if n is not None and n <= ciphertext_len:
			ciphertext = memoryview(self.ciphertext)[
					self.ciphertext_i:self.ciphertext_i+n]
			self.ciphertext_i += n
			if n == ciphertext_len and n > 0:
				self.ciphertext = bytearray()
				self.ciphertext_i = 0
			return ciphertext

		# Trim the bytes from @self.ciphertext that have been returned
		# above.
		if self.ciphertext_i > 0:
			try:
				del self.ciphertext[:self.ciphertext_i]
			except BufferError:
				# There could be an "Existing exports of data:
				# object cannot be re-sized" error if a view
				# of @self.ciphertext returned earlier is still
				# held somewhere in the program.
				self.ciphertext = \
					self.ciphertext[self.ciphertext_i:]
			self.ciphertext_i = 0

		# Encrypt new chunks of cleartext and add them
		# to @self.ciphertext.
		while (n is None or len(self.ciphertext) < n) and not self.eof:
			cleartext = bytearray()
			max_cleartext = self.CLEARTEXT_SIZE
			new_bulk_key = None
			if not self.chunk_counter:
				# We've already added the init block to
				# @self.ciphertext, so we'll need to add
				# fewer bytes to the @cleartext if we want
				# @self.ciphertext to be CIPHERTEXT_SIZE
				# at most after the first chunk.
				max_cleartext -= self.init_block_size()
			elif self.chunk_counter % self.CHUNKS_PER_STRIPE == 0:
				new_bulk_key = self.gen_bulk_key()
				cleartext += new_bulk_key

			# Read up to @max_cleartext from @self.wrapped.
			min_cleartext = len(cleartext)
			while len(cleartext) < max_cleartext:
				prev_cleartext = len(cleartext)
				to_read = max_cleartext - prev_cleartext
				try:
					cleartext += self.wrapped.read(to_read)
				except OSError as ex:
					raise FatalError(
						"couldn't read cleartext:",
						ex.strerror) from ex

				nread = len(cleartext) - prev_cleartext
				if not nread:
					self.eof = True
					break
				self.bytes_in += nread

			assert len(cleartext) <= max_cleartext
			if len(cleartext) == min_cleartext:
				# Couldn't get more data from @self.wrapped.
				assert self.eof
				break
			assert len(cleartext) == max_cleartext or self.eof

			self.ciphertext += self.encrypt_base(
							self.bulk_cipher,
							self.next_bulk_nonce(),
							cleartext)

			if new_bulk_key is not None:
				self.bulk_cipher = self.bulk_cipher_class(
								new_bulk_key)

		# Return the first @n bytes of @self.ciphertext or all of it.
		if n is not None and n < len(self.ciphertext):
			ciphertext = memoryview(self.ciphertext)[:n]
			self.ciphertext_i = n
		else:
			ciphertext = self.ciphertext
			if self.ciphertext:
				self.ciphertext = bytearray()

		return ciphertext

	# Verify that @self.wrapper has been read and processed fully.
	def close(self):
		if self.borked is None:
			assert self.eof
			assert not self.ciphertext
		self.wrapped.close()

class InternalDecrypt(InternalCipher):
	# The input buffer.
	ciphertext: bytearray

	def __init__(self,
			meta_cipher: Primitive,
			bulk_cipher_class: type[Primitive],
			blob_uuid: uuid.UUID, data_type_id: int,
			wrapped: Optional[BinaryIO] = None):
		super().__init__(meta_cipher, bulk_cipher_class,
					blob_uuid, data_type_id, wrapped)

	def reset(self, blob_uuid: Optional[uuid.UUID] = None,
			data_type_id: Optional[int] = None,
			wrapped: Optional[BinaryIO] = None) -> None:
		super().reset(blob_uuid, data_type_id, wrapped)
		self.ciphertext = bytearray()

	# Abstraction to invoke the @cipher's decryption function.
	def decrypt_base(self, cipher: Primitive, nonce: ByteString,
				ciphertext: ByteString) -> bytes:
		from cryptography import exceptions as cryptography_exceptions

		try:
			if isinstance(cipher, self.aead.AESSIV):
				auth_data = [ self.auth_data, nonce ]
				cleartext = cipher.decrypt(ciphertext,
								auth_data)
			else:
				cleartext = cipher.decrypt(nonce, ciphertext,
							self.auth_data)
		except cryptography_exceptions.InvalidTag as ex:
			raise SecurityError(
				"Decryption of ciphertext block "
				"at offset %d failed" % self.bytes_in) \
				from ex

		self.bytes_in += len(ciphertext)
		return cleartext

	# Decrypt the @ciphertext with the @self.meta_cipher.
	def decrypt_meta(self, ciphertext: ByteString) -> bytes:
		assert len(ciphertext) >= self.NONCE_SIZE

		ciphertext = memoryview(ciphertext)
		cleartext = self.decrypt_base(self.meta_cipher,
						ciphertext[:self.NONCE_SIZE],
						ciphertext[self.NONCE_SIZE:])
		self.bytes_in += self.NONCE_SIZE

		return cleartext

	# Decrypt a chunk of @ciphertext and write it to @self.wrapped.
	def decrypt_bulk(self, ciphertext: ByteString) -> None:
		rekey_bulk_cipher = self.chunk_counter > 0 \
					and self.chunk_counter \
						% self.CHUNKS_PER_STRIPE == 0
		cleartext = self.decrypt_base(self.bulk_cipher,
						self.next_bulk_nonce(),
						ciphertext)

		if rekey_bulk_cipher:
			# Time to create a new @self.bulk_cipher.
			bulk_key_size = self.bulk_key_size()
			assert len(cleartext) >= bulk_key_size

			# The new key is the first @bulk_key_size bytes
			# of the @cleartext.
			cleartext = memoryview(cleartext)
			self.bulk_cipher = self.bulk_cipher_class(
						cleartext[:bulk_key_size])
			cleartext = cleartext[bulk_key_size:]

		if self.wrapped is not None:
			try:
				self.wrapped.write(cleartext)
			except OSError as ex:
				raise FatalError(
					"couldn't write cleartext:",
					ex.strerror) from ex
		self.bytes_out += len(cleartext)

	# Add bytes from @buf to @self.ciphertext until it reaches
	# @ciphertext_size.  Return None if @buf is too small, otherwise
	# return the number of bytes consumed from @buf.
	def load_ciphertext(self, buf: ByteString, ciphertext_size: int) \
				-> Optional[int]:
		assert ciphertext_size > len(self.ciphertext)
		n = ciphertext_size - len(self.ciphertext)

		if len(buf) < n:
			self.ciphertext += buf
			return None
		else:
			self.ciphertext += buf[:n]
			return n

	# Return how much data to decrypt next.
	def next_chunk_size(self) -> int:
		ciphertext_size = self.CIPHERTEXT_SIZE
		if self.chunk_counter == 0:
			# We're about to decrypt the first chunk
			# (right after the init block).
			ciphertext_size -= self.init_block_size()
		return ciphertext_size

	# Decrypt as much as we can of @buf, writing the cleartext to
	# @self.wrapped, then add the remainder of @buf to @self.ciphertext.
	# In case of an exception this function is not retryable because
	# the internal state is not updated atomically.
	@InternalCipher.noretry
	def write(self, buf: ByteString) -> None:
		if not isinstance(buf, memoryview):
			buf = memoryview(buf)

		if self.bulk_cipher is None:
			# Extract the init block.
			init_block_size = self.init_block_size()
			buf_i = self.load_ciphertext(buf, init_block_size)
			if buf_i is None:
				return

			# Create the first stripe's @self.bulk_cipher.
			cleartext = memoryview(self.decrypt_meta(
							self.ciphertext))
			bulk_key_size = self.bulk_key_size()
			self.bulk_cipher = self.bulk_cipher_class(
						cleartext[:bulk_key_size])
			self.init_prng(int.from_bytes(
						cleartext[bulk_key_size:]))

			self.ciphertext = bytearray()
		elif self.ciphertext:
			# Consume @self.ciphertext.
			ciphertext_size = self.next_chunk_size()
			buf_i = self.load_ciphertext(buf, ciphertext_size)
			if buf_i is None:
				return

			assert len(self.ciphertext) == ciphertext_size
			self.decrypt_bulk(self.ciphertext)
			self.ciphertext = bytearray()
		else:
			buf_i = 0

		# Consume the rest of @buf.
		assert not self.ciphertext
		while True:
			ciphertext_size = self.next_chunk_size()
			if len(buf) - buf_i < ciphertext_size:
				self.ciphertext += buf[buf_i:]
				break

			self.decrypt_bulk(buf[buf_i:buf_i+ciphertext_size])
			buf_i += ciphertext_size

	# Flush @self.ciphertext and close @self.wrapped.  Must be called
	# before disposing of the object.
	def close(self) -> None:
		if self.ciphertext and self.borked is None:
			self.decrypt_bulk(self.ciphertext)
			self.ciphertext = bytearray()
		if self.wrapped is not None:
			self.wrapped.close()
# }}}

# A class abstracting the details of internal vs. external encryption away.
class MetaCipher: # {{{
	class DataType(enum.IntEnum):
		PAYLOAD		= 0
		METADATA	= 1
		SIGNATURE	= 2

		def field(self):
			return self.name.lower()

	args: EncryptionOptions

	# Must be set for any encryption/decryption.  May be left None if the
	# subclass doesn't need to do either of them.
	blob_uuid: Optional[uuid.UUID]

	# Cleartext header for external encryption, proving which blob
	# and DataType it was encrypted for.
	external_header_st: Final[struct.Struct] = \
		struct.Struct(f"!{BTRFS_UUID_SIZE}sI")

	def __init__(self, args: EncryptionOptions,
			blob_uuid: Optional[uuid.UUID] = None):
		self.args = args
		self.blob_uuid = blob_uuid

	def get_cipher_cmd_env(self) -> dict[str, str]:
		env = os.environ.copy()

		assert self.args.volume is not None
		env["GICCS_VOLUME"] = self.args.volume

		return env

	def get_key(self) -> Optional[bytes]:
		if self.args.encryption_key is None:
			if self.args.encryption_key_command is None:
				return None
			self.args.encryption_key = subprocess_check_output(
					self.args.encryption_key_command,
					env=self.get_cipher_cmd_env())

		# Require at least a 128-bit key.
		if len(self.args.encryption_key) < 16:
			raise UserError(
				"encryption-key too short "
				"(%d bytes, should be at least 16)"
				% len(self.args.encryption_key))

		return self.args.encryption_key

	InternalCipherClass = TypeVar("InternalCipherClass",
					bound=InternalCipher)
	def internal_cipher(self,
			internal_cipher_class: type[InternalCipherClass],
			data_type: DataType,
			wrapped: Optional[BinaryIO] = None) \
			-> InternalCipherClass:
		assert self.args.encrypt_internal()

		key = self.get_key()
		assert key is not None

		try:
			meta_cipher = self.args.meta_cipher(key)
		except ValueError as ex:
			# Invalid key length.
			raise UserError(ex) from ex

		assert self.blob_uuid is not None
		return internal_cipher_class(
				meta_cipher, self.args.bulk_cipher,
				self.blob_uuid, data_type.value,
				wrapped=wrapped)

	def internal_encrypt(self, data_type: DataType,
				src: Optional[BinaryIO] = None) \
				-> InternalEncrypt:
		return self.internal_cipher(InternalEncrypt, data_type, src)

	def internal_decrypt(self, data_type: DataType,
				dst: Optional[BinaryIO] = None) \
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
		assert self.blob_uuid is not None
		return self.external_header_st.pack(
					self.blob_uuid.bytes,
					data_type.value)

	# Encrypt a short piece of metadata.
	def encrypt(self, data_type: DataType, cleartext: ByteString) \
			-> bytes:
		if self.args.encrypt_internal():
			return self.internal_encrypt(data_type) \
					.encrypt_meta(cleartext)
		else:	# @self.args.add_header_to_blob is pointedly ignored
			# for the meaningful security for metadata.
			header = self.external_header(data_type)
			return subprocess_check_output(
				**self.external_encrypt(),
				input=header + cleartext)

	# Decrypt metadata.
	def decrypt(self, data_type: DataType, ciphertext: ByteString) \
			-> Union[bytes, memoryview]:
		if self.args.encrypt_internal():
			return self.internal_decrypt(data_type) \
					.decrypt_meta(ciphertext)

		# External encryption.
		cleartext = memoryview(subprocess_check_output(
					**self.external_decrypt(),
					input=ciphertext))

		# Verify the header.
		if len(cleartext) < self.external_header_st.size:
			raise SecurityError("Incomplete cleartext header")
		recv_uuid, recv_data_type = \
			self.external_header_st.unpack_from(cleartext)

		assert self.blob_uuid is not None
		if recv_uuid != self.blob_uuid.bytes:
			raise SecurityError(
				"Cleartext header mismatch: "
				"blob UUID (%s) differs from "
				"expected (%s)"
				% (uuid.UUID(bytes=recv_uuid), self.blob_uuid))

		if recv_data_type != data_type.value:
			raise SecurityError(
				"Cleartext header mismatch: "
				"data type (0x%.2X) differs from "
				"expected (0x%.2X)"
				% (recv_data_type, data_type.value))

		return cleartext[self.external_header_st.size:]
# }}}

# Provide a MAC either through BLAKE2 natively or by encrypting the hash
# with the MetaCipher.
class MetaMAC: # {{{
	# hashlib doesn't define an abstract base class, let's have our own.
	class Hasher(Protocol):
		def update(self, data: bytes) -> None:
			...

		def digest(self) -> bytes:
			...

	hasher: Hasher
	meta: Optional[MetaCipher]
	data_type: MetaCipher.DataType

	def __init__(self, meta: MetaCipher, data_type: MetaCipher.DataType):
		self.data_type = data_type
		persona = self.data_type.value.to_bytes(4)

		key = meta.get_key()
		if key is not None:
			self.meta = None
			self.hasher = hashlib.blake2b(
					meta.blob_uuid.bytes,
					key=key, person=persona)
		else:
			self.meta = meta
			self.hasher = hashlib.blake2b(person=persona)

	def update(self, data: bytes) -> None:
		self.hasher.update(data)

	def sign(self) -> bytes:
		digest = self.hasher.digest()
		if self.meta is None:
			# @self.hasher is keyed.
			return digest

		# It should be safe to use an encrypted hash as a MAC,
		# since we expect it to be integrity-protected.
		return self.meta.encrypt(self.data_type, digest)

	def verify(self, signature: bytes) -> bool:
		if self.meta is not None:
			digest = self.meta.decrypt(self.data_type, signature)
		else:
			digest = signature

		return hmac.compare_digest(self.hasher.digest(), digest)
# }}}

# A GCS blob with metadata.
class MetaBlob(MetaCipher): # {{{
	T = TypeVar("MetaBlobType", bound=Self)

	# Classes to try in create_best_from_gcs().
	subclasses: list[T] = [ ]

	gcs_blob: google.cloud.storage.Blob

	# The user-visible path of the blob without a leading /.
	# If metadata is not encrypted, it's the same as the @blob_name
	# without @args.prefix.
	user_path: pathlib.PurePath

	# The time when the blob was last changed by us.
	user_mtime: datetime.datetime

	# The size of the payload before compression and encryption.
	user_size: Optional[int] = None

	# The end-to-end hash computed by the Progressometer.  This provides
	# an additional layer of defense against reordering stripes within
	# blobs or replacing them across blobs.
	blob_hash: Optional[bytes] = None

	# Padding added to the payload after compression and encryption,
	# generated from @padding_seed.
	padding: int = 0
	padding_seed: Optional[bytes] = None

	# Class decorator to register a subclass for create_best_from_gcs().
	@classmethod
	def register_subclass(cls, subclass: T):
		cls.subclasses.append(subclass)
		return subclass

	# The GCS-visible name of the blob.
	@property
	def blob_name(self) -> str:
		return self.gcs_blob.name

	@property
	def blob_size(self) -> int:
		return self.gcs_blob.size

	@property
	def volume(self) -> str:
		return self.args.volume

	# Can an instance of @cls represent a blob with these @metadata?
	# Should be overridden by subclasses.
	@classmethod
	def isa(cls, metadata: Optional[dict[str, Any]]) -> bool:
		return True

	def __str__(self):
		return str(self.user_path)

	def __init__(self, args: EncryptedBucketOptions,
			user_path: pathlib.PurePath,
			backups: Optional[Backups] = None, **kw):
		super().__init__(args)

		while True:
			if not args.encrypt:
				pass
			elif args.random_blob_uuid:
				# Generate a fully random @self.blob_uuid.
				# It is very unlikely, though possible, that
				# the UUID won't be unique and the server lies
				# about it, which is highly undesirable by us.
				self.blob_uuid = uuid.uuid4()
			else:	# To avoid that possibility, mix in the local
				# time. This leaks information, but the server
				# will be aware of the creation time anyway.
				uuid_bytes = \
					(int(time.time()) & 0xFFFFFFFF) \
					.to_bytes(4)
				uuid_bytes += secrets.token_bytes(
					len(UUID0.bytes) - len(uuid_bytes))
				self.blob_uuid = uuid.UUID(bytes=uuid_bytes)

			blob_name = args.prefix
			blob_name /= str(self.blob_uuid) \
					if args.encrypt_metadata \
					else user_path
			assert not blob_name.is_absolute()

			self.gcs_blob = args.bucket.blob(str(blob_name))
			if not args.encrypt:
				assert self.blob_uuid is None
				break
			elif backups is not None \
					and self.blob_uuid in backups.blobs:
				# The generated @self.blob_uuid conflicts
				# with an existing one.
				continue
			elif args.encrypt_metadata and self.gcs_blob.exists():
				# Likewise.
				continue
			else:
				break

		self.init_metadata(user_path, **kw)
		self.update_metadata()

	# Try to create a MetaBlob or a subclass thereof and set it up
	# to represent @gcs_blob.
	@classmethod
	def create_from_gcs_with_metadata(
			cls, args: EncryptedBucketOptions,
			gcs_blob: google.cloud.storage.Blob,
			blob_uuid: Optional[uuid.UUID] = None,
			metadata: Optional[dict[str, Any]] = None) \
			-> tuple[
				Optional[T],
				Optional[uuid.UUID],
				Optional[dict[str, Any]]]:
		self, blob_uuid, metadata = cls.create_self(
			args, gcs_blob, blob_uuid, metadata)
		if self is None:
			return self, blob_uuid, metadata

		self.load_metadata(metadata)
		if self.has_signature():
			# We can only verify the signature once all metadata
			# has been loaded.
			signature = self.load_metadatum(metadata, "signature",
							bytes)
			if not self.calc_signature().verify(signature):
				raise SecurityError(
					"%s: metadata/signature mismatch"
					% self.blob_name)
		else:	# Assert that there's no signature in @metadata,
			# otherwise there's a possible misconfiguration.
			self.has_metadatum(metadata, "signature", False)

		if self.load_metadatum(metadata, "volume") != self.volume:
			return None, blob_uuid, metadata

		return self, blob_uuid, metadata

	# Return an instance of @cls if it can represent this @gcs_blob.
	# If @blob_uuid and @metadata are not provided, they are obtained
	# from @gcs_blob and returned for future reuse.
	@classmethod
	def create_self(cls, args: EncryptedBucketOptions,
			gcs_blob: google.cloud.storage.Blob,
			blob_uuid: Optional[uuid.UUID] = None,
			metadata: Optional[dict[str, Any]] = None) \
			-> tuple[
				Optional[T],
				Optional[uuid.UUID],
				Optional[dict[str, Any]]]:
		if not args.encrypt_metadata:
			assert blob_uuid is None
			if metadata is None:
				# @metadata is stored directly
				# with the @gcs_blob.
				metadata = gcs_blob.metadata
			else:
				assert metadata == gcs_blob.metadata
			if not cls.isa(metadata):
				return None, blob_uuid, metadata

		self = super().__new__(cls)
		super().__init__(self, args)
		self.gcs_blob = gcs_blob

		if args.encrypt_metadata:
			self.init_blob_uuid(blob_uuid)
			if metadata is None:
				metadata = self.init_encrypted_metadata()

			if not self.isa(metadata):
				return None, self.blob_uuid, metadata

		return self, self.blob_uuid, metadata

	# Initialize @self.blob_uuid either from @blob_uuid or @self.blob_name.
	def init_blob_uuid(self, blob_uuid: Optional[uuid.UUID] = None) \
				-> None:
		assert self.args.encrypt_metadata

		if blob_uuid is not None:
			self.blob_uuid = blob_uuid
			return

		blob_uuid = self.args.without_prefix(self.blob_name)
		try:
			self.blob_uuid = uuid.UUID(blob_uuid)
		except ValueError as ex:
			# If a volume has a prefix, all volumes
			# in the bucket must have a prefix too.
			raise ConsistencyError(
				"%s has invalid UUID (%s), "
				"maybe you need to specify a --prefix"
				% (self.blob_name, blob_uuid)) from ex

		# A UUID can be represented textually in many ways,
		# for example with curly braces.  Verify that @blob_uuid
		# is in the default representation.  It wouldn't do harm
		# if we accepted any representation, but a difference
		# could indicate tampering.
		expected = str(self.args.prefix / str(self.blob_uuid))
		if self.blob_name != expected:
			raise SecurityError(
				f"{self.blob_name} is denormalized, "
				f"should be {expected}")

	# Decrypt and decode @self.gcs_blob.metadata["metadata"].
	def init_encrypted_metadata(self) -> dict[str, Any]:
		import pickle

		assert self.args.encrypt_metadata
		metadata = self.decrypt(self.DataType.METADATA,
					self.load_metadatum(
						self.gcs_blob.metadata,
						"metadata", bytes))

		try:	# @metadata has been authenticated, so it's safe
			# to unpickle it.
			metadata = pickle.loads(metadata)
		except pickle.PickleError as ex:
			raise SecurityError(
				"%s[%s]: couldn't decode metadata"
				% (self.blob_name, "metadata")) from ex

		if not isinstance(metadata, dict):
			raise SecurityError(
				"%s[%s]: invalid metadata"
				% (self.blob_name, "metadata"))

		return metadata

	# Return an instance of MetaBlob or a subclass thereof that represents
	# @gcs_blob the best.
	@classmethod
	def create_best_from_gcs(
			cls, args: EncryptedBucketOptions,
			gcs_blob: google.cloud.storage.Blob,
			subclasses: Union[
				None, type[T], Iterable[type[T]]
			] = None) -> Optional[T]:
		if subclasses is None:
			# Choose from the registered subclasses.
			subclasses = cls.subclasses
		elif issubclass(subclasses, __class__):
			# Only one subclass was provided.
			subclasses = (subclasses,)

		blob_uuid = metadata = None
		for subclass in subclasses:
			self, blob_uuid, metadata = \
				subclass.create_from_gcs_with_metadata(
					args, gcs_blob, blob_uuid, metadata)
			if self is not None:
				return self

		# Don't try MetaBlob implicitly if @subclasses were provided.
		if subclasses is not cls.subclasses:
			return None
		return __class__.create_from_gcs_with_metadata(
				args, gcs_blob, blob_uuid, metadata)[0]

	# Return an instance of @cls if it can represent this @gcs_blob.
	# Use it if you want to create an object from a particular class.
	@classmethod
	def create_from_gcs(
			cls, args: EncryptedBucketOptions,
			gcs_blob: google.cloud.storage.Blob) -> Optional[T]:
		return cls.create_from_gcs_with_metadata(args, gcs_blob)[0]

	# Called by __init__() to initialize metadata fields.
	def init_metadata(self, user_path: pathlib.PurePath, **kw) -> None:
		self.user_path = user_path

		# We need to make this timezone-aware, so str(self.user_mtime)
		# will include the timezone, and datetime.fromisoformat()
		# will restore it properly.
		self.user_mtime = datetime.datetime.now(datetime.timezone.utc)

	# Called by create_from_gcs_with_metadata() to restore metadata fields
	# from @metadata.
	def load_metadata(self, metadata: Optional[dict[str, Any]]) -> None:
		# Don't load @metadata["volume"], we already have our
		# expectation in @self.args.volume.

		if self.has_signature():
			assert self.blob_uuid is None
			self.blob_uuid = self.load_metadatum(metadata,
								"blob_uuid",
								uuid.UUID)

		if self.args.encrypt_metadata:
			self.user_path = self.load_metadatum(metadata,
						"user_path", pathlib.PurePath)
		else:
			self.user_path = \
				pathlib.PurePath(
					self.args.without_prefix(
							self.blob_name))

			# Do the same cross-check as in init_blob_uuid().
			expected = str(self.args.prefix / self.user_path)
			if self.blob_name != expected:
				raise SecurityError(
					f"{self.blob_name} is denormalized")

		self.user_mtime = self.load_metadatum(metadata,
						"mtime", datetime.datetime)

		expected = self.args.integrity >= self.args.Integrity.SIZE
		blob_size = self.load_metadatum(
					metadata, "blob_size", int,
					expected=expected)
		if blob_size is not None and self.blob_size != blob_size:
			raise SecurityError(
				"%s has unexpected size (%d != %d)"
				% (self.blob_name, self.blob_size, blob_size))

		self.user_size = self.load_metadatum(metadata, "user_size",
							int, expected=False)

		expected = self.args.integrity >= self.args.Integrity.HASH
		self.blob_hash = self.load_metadatum(
					metadata, "blob_hash", bytes,
					expected=expected)

		self.padding = self.load_metadatum(
					metadata, "padding",
					int, expected=False) or 0
		self.padding_seed = self.load_metadatum(
					metadata, "padding_seed", bytes,
					expected=self.padding > 0)

	# Called by update_metadata() to save metadata fields in @metadata.
	def save_metadata(self, metadata: dict[str, Any]) -> None:
		self.save_metadatum(metadata, "volume", self.volume)

		if self.has_signature():
			self.save_metadatum(metadata,
						"blob_uuid", self.blob_uuid)
		if self.args.encrypt_metadata:
			self.save_metadatum(metadata,
						"user_path", self.user_path)

		self.save_metadatum(metadata, "mtime", self.user_mtime)

		if self.args.encrypt:
			self.save_metadatum(metadata,
						"blob_size", self.blob_size)
		self.save_metadatum(metadata, "user_size", self.user_size)

		self.save_metadatum(metadata, "blob_hash", self.blob_hash)

		self.save_metadatum(metadata, "padding", self.padding or None)
		self.save_metadatum(metadata, "padding_seed", self.padding_seed)

		if self.has_signature():
			self.save_metadatum(
				metadata, "signature",
				self.calc_signature().sign())

	# Initialize or update @self.gcs_blob.metadata.
	# Returns whether the metadata needs to be synced.
	def update_metadata(self) -> bool:
		gcs_metadata = self.gcs_blob.metadata
		if gcs_metadata is None:
			gcs_metadata = { }

		metadata = { } if self.args.encrypt_metadata else gcs_metadata
		self.save_metadata(metadata)

		if self.args.encrypt_metadata:
			# Save all @metadata in a pickle.
			import pickle
			self.save_metadatum(
				gcs_metadata, "metadata",
				self.encrypt(
					self.DataType.METADATA,
					pickle.dumps(metadata)),
				text=True)

		if self.gcs_blob.metadata != gcs_metadata:
			self.gcs_blob.metadata = gcs_metadata
			return True
		else:
			return False

	# Write new metadata to @self.gcs_blob.
	def sync_metadata(self, update_mtime: bool = True) -> None:
		if update_mtime:
			self.user_mtime = datetime.datetime.now(
							datetime.timezone.utc)

		# Patching costs money, so avoid it if we can.
		if self.update_metadata():
			self.gcs_blob.patch()

	# Return whether the blob should have a "signature" metadata.
	def has_signature(self) -> bool:
		# If the metadata is encrypted we assume it is authenticated,
		# so it doesn't need a separate signature.
		return self.args.encrypt and not self.args.encrypt_metadata

	# Calculate a hash of metadata fields.
	def calc_signature(self) -> MetaMAC:
		hasher = MetaMAC(self, self.DataType.SIGNATURE)

		hasher.update(self.volume.encode())
		hasher.update(b'\0')

		# @self.blob_uuid is included by the @hasher automatically.
		hasher.update(bytes(self.args.prefix / self.user_path))
		hasher.update(b'\0')

		for size in (self.blob_size, self.user_size):
			if size is None:
				# Use an unlikely value.
				size = (1 << 8*8) - 1
			hasher.update(size.to_bytes(8, "big"))

		# @self.user_mtime.timestamp() is a float.
		hasher.update(struct.pack(">d", self.user_mtime.timestamp()))

		hasher.update(self.padding.to_bytes(8, "big"))
		hasher.update(self.padding_seed if self.padding_seed is not None
				else b'\0' * CSPRNG.DFLT_SEED_SIZE)

		hasher.update(self.blob_hash if self.blob_hash is not None
				else b'\0' * 64)

		return hasher

	# Return whether @key is in @metadata.  If @expected is True,
	# it must be present.  If False, it must not be present.
	def has_metadatum(self, metadata: Optional[dict[str, Any]],
				key: str, expected: Optional[bool] = None) \
				-> bool:
		if metadata is not None and key in metadata:
			if expected is False:
				raise ConsistencyError(
						"%s[%s]: unexpected metadata"
						% (self.blob_name, key))
			return True
		else:
			if expected is True:
				raise SecurityError(
						"%s[%s]: missing metadata"
						% (self.blob_name, key))
			return False


	# Return @metadata[@key] converted to @tpe or None if @key is not
	# in @metadata.
	def load_metadatum(self, metadata: Optional[dict[str, Any]],
				key: str, tpe: type[MDT] = str,
				expected: bool = True) -> Optional[MDT]:
		if not self.has_metadatum(metadata, key, expected or None):
			return None

		value = metadata[key]
		if isinstance(value, tpe):
			return value

		if tpe is uuid.UUID and isinstance(value, bytes):
			try:
				return uuid.UUID(bytes=value)
			except ValueError as ex:
				raise SecurityError(
					"%s[%s]: invalid metadata"
					% (self.blob_name, key)) from ex
		elif tpe is datetime.datetime \
				and isinstance(value, (int, float)):
			return datetime.datetime.fromtimestamp(value)

		assert isinstance(value, str)
		if tpe is bytes:
			try:
				return base64.b64decode(value, validate=True)
			except binascii.Error as ex:
				raise SecurityError(
					"%s[%s]: couldn't decode metadata"
					% (self.blob_name, key)) from ex
		else:	# @tpe is either int, pathlib.PurePath, uuid.UUID
			# or datetime.datetime.
			try:
				if tpe is datetime.datetime:
					return datetime.datetime \
							.fromisoformat(value)
				else:
					return tpe(value)
			except ValueError as ex:
				raise SecurityError(
					"%s[%s]: invalid metadata"
					% (self.blob_name, key)) from ex

	# If @value is None, delete @key from @metadata, otherwise set
	# @metadata[@key] to @value.  If @text, convert @value to string
	# beforehand.
	MDT = TypeVar("MetadataType", int, str, bytes,
					pathlib.PurePath, uuid.UUID,
					datetime.datetime)
	def save_metadatum(self,
			metadata: dict[str, Any],
			key: str, value: Optional[Union[MDT, ByteString]],
			text: Optional[bool] = None) -> None:
		if value is None:
			try: del metadata[key]
			except KeyError: pass
			return

		if text is None:
			text = not self.args.encrypt_metadata
		if text:
			# Convert to string.  For some reason a memoryview
			# is not an instance of ByteString, even though the
			# documentation of the typing module says so.
			if isinstance(value, (ByteString, memoryview)):
				metadata[key] = b64encode(value)
			else:
				metadata[key] = str(value)
		else:	# Convert to a primitive type for pickling.
			if isinstance(value, pathlib.PurePath):
				metadata[key] = str(value)
			elif isinstance(value, uuid.UUID):
				metadata[key] = value.bytes
			elif isinstance(value, datetime.datetime):
				metadata[key] = value.timestamp()
			elif isinstance(value, (int, str, bytes)):
				metadata[key] = value
			else:	# bytearray or memoryview
				metadata[key] = bytes(value)

	# A wrapper around MetaCipher.decrypt(), enhancing the error message.
	def decrypt(self, data_type: MetaCipher.DataType,
			ciphertext: ByteString) -> Union[bytes, memoryview]:
		try:
			return super().decrypt(data_type, ciphertext)
		except FatalError as ex:
			pfx = "%s[%s]:" % (self.blob_name, data_type.field())
			raise ex.__class__(pfx, ex) from ex
# }}}

# A MetaBlob of a Backup.
@MetaBlob.register_subclass
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

	@classmethod
	def isa(cls, metadata: Optional[dict[str, Any]]) -> bool:
		return metadata and "snapshot_uuid" in metadata

	def __init__(self, args: EncryptedBucketOptions,
			payload_type: PayloadType,
			snapshot: Snapshot, parent: Optional[Snapshot],
			backups: Backups):
		super().__init__(args, pathlib.PurePath(snapshot.snapshot_name,
							payload_type.field()),
					backups, payload_type=payload_type,
					snapshot=snapshot, parent=parent)

	def init_metadata(self, user_path: pathlib.PurePath,
				payload_type: PayloadType,
				snapshot: Snapshot,
				parent: Optional[Snapshot]) -> None:
		super().init_metadata(user_path)

		self.snapshot_name = snapshot.snapshot_name
		self.snapshot_uuid = snapshot.snapshot_uuid

		self.payload_type = payload_type
		if payload_type == self.PayloadType.DELTA:
			assert parent is not None
			self.parent_uuid = parent.snapshot_uuid
		else:
			assert parent is None
			self.parent_uuid = None

	def save_metadata(self, metadata: dict[str, Any]) -> None:
		super().save_metadata(metadata)
		self.save_metadatum(metadata, "snapshot_uuid",
						self.snapshot_uuid)
		self.save_metadatum(metadata, "parent_uuid", self.parent_uuid)

	def load_metadata(self, metadata: Optional[dict[str, Any]]) -> None:
		super().load_metadata(metadata)

		if len(self.user_path.parts) < 2:
			raise ConsistencyError(
				f"{self.blob_name}'s path is missing "
				"payload type")
		self.snapshot_name, payload_type = self.user_path.parts[-2:]

		if not payload_type.islower():
			raise ConsistencyError(
				f"{self.blob_name}'s path has invalid "
				f"payload type ({payload_type})")
		payload_type = payload_type.upper()
		try:
			self.payload_type = self.PayloadType[payload_type]
		except KeyError:
			raise ConsistencyError(
				f"{self.blob_name} has unknown "
				f"payload type ({payload_type})")

		self.snapshot_uuid = self.load_metadatum(
						metadata, "snapshot_uuid",
						uuid.UUID)
		if self.payload_type == self.PayloadType.DELTA:
			self.parent_uuid = self.load_metadatum(
						metadata, "parent_uuid",
						uuid.UUID)
		else:
			self.has_metadatum(metadata, "parent_uuid", False)
			self.parent_uuid = None

	def calc_signature(self) -> MetaMAC:
		hasher = super().calc_signature()

		hasher.update(self.snapshot_uuid.bytes)
		hasher.update(ensure_uuid(self.parent_uuid).bytes)

		return hasher
# }}}

# A class that proxies the read()s and write()s of the GCS library
# to the wrapped file-like object.  It has several responsibilities:
#
#   * Keep track of the @transferred_gross so far, and print it periodically.
#   * If the @expected_gross is known beforehand, ensure that GCS returns
#     exactly as much data to us, no more or less.
#   * Add padding to the transferred data when uploading and verify it when
#     downloading.
#   * Calculate the hash of the transferred data and verify it against the
#     @expected_hash at the end.
class Progressometer: # {{{
	# The file we'll ultimately read() from or write() to.  If None,
	# write() will simply discard what it would have written.
	wrapped: Optional[BinaryIO]

	# If not None, the minimum number of seconds between showing progress.
	interval: Optional[float]

	# The number of bytes (including padding) read() will return or write()
	# will accept.  Could be None if we don't know it yet or not at all.
	expected_gross: Optional[int]

	# A user-specified callback to invoke before read() returns for the
	# last time.
	final_cb: Optional[Callable[[], None]]

	# Used to decide when to print a new progress.
	started: Optional[float] = None
	last_checkpoint_time: Optional[float] = None
	last_checkpoint_bytes: Optional[int] = None

	# The minimum time read() and write() should take to finish to make it
	# harder for the server to infer anything from time measurements, like
	# how much the data is compressible or whether it's receiving padding
	# bytes.  This field is managed by delay().
	minlag: Optional[float] = None

	# The number of bytes (including padding) returned by read() or taken
	# by write() so far.
	transferred_gross: int = 0

	# If not None, add or expect padding.  It could be a concreate number
	# of bytes, or the algorithm to calculate it from when the number of
	# non-padding bytes becomes known (ie. when we've consumed the @wrapped
	# file).
	class Padding(Choices, enum.Enum):
		PADME		= enum.auto()
		COVERT		= enum.auto()
	padding: Optional[Union[Padding, int]] = None

	# The generator of random padding bytes.
	csprng: Optional[CSPRNG] = None

	# The hasher used to calculate and possibly verify the hash of the
	# transferred bytes (including padding).
	hasher: Optional[MetaMAC.Hasher] = None
	expected_hash: Optional[bytes] = None

	def __init__(self, f: Optional[BinaryIO],
			interval: Optional[float],
			expected_net: Optional[int] = None,
			expected_gross: Optional[int] = None,
			padding: Optional[Union[Padding, int]] = None,
			padding_seed: Optional[bytes] = None,
			hashing: Optional[Union[bool, bytes]] = None,
			final_cb: Optional[Callable[[], None]] = None,
			autolag: bool = False):
		self.wrapped = f
		self.interval = interval
		self.final_cb = final_cb

		self.padding = padding
		self.expected_gross = expected_gross
		if expected_net is not None and expected_gross is not None:
			assert expected_net <= expected_gross
			self.padding = self.calc_padding(expected_net)
			assert self.padding == expected_gross - expected_net
		elif expected_net is not None:
			self.padding = self.calc_padding(expected_net)
			self.expected_gross = expected_net + self.padding
		elif expected_gross is not None:
			self.padding = self.calc_padding()
		if self.padding:
			self.csprng = CSPRNG(seed=padding_seed)

		if hashing is not None:
			persona = MetaCipher.DataType.PAYLOAD.value.to_bytes(4)
			self.hasher = hashlib.blake2b(person=persona)
			if isinstance(hashing, bytes):
				self.expected_hash = hashing

		if autolag:
			self.minlag = 0

	def make_progress(self) -> None:
		progress = humanize_size(self.transferred_gross)
		if self.expected_gross is not None:
			assert self.transferred_gross <= self.expected_gross
			done = self.transferred_gross / self.expected_gross
			progress = "%d%% (%s)" % (int(done * 100), progress)
		print(f" %s..." % progress, end="", flush=True)

	def check_progress(self, now: float) -> None:
		if self.interval is None:
			return

		if self.last_checkpoint_time is None:
			self.started = now
			self.last_checkpoint_time = now
		elif now - self.last_checkpoint_time >= self.interval \
				and self.last_checkpoint_bytes \
					!= self.transferred_gross:
			self.make_progress()
			self.last_checkpoint_time = now
			self.last_checkpoint_bytes = self.transferred_gross

	def delay(self, started: float) -> None:
		if self.minlag is None:
			return

		elapsed = time.monotonic() - started
		if self.minlag > elapsed:
			time.sleep(self.minlag - elapsed)
		else:
			self.minlag = elapsed

	# Called by the user when it's finished with reading/writing.
	def final_progress(self) -> None:
		if self.expected_gross is not None:
			assert self.transferred_gross <= self.expected_gross
			if self.transferred_gross < self.expected_gross:
				missing = self.expected_gross \
						- self.transferred_gross
				raise SecurityError(
					f"Blob is missing {missing} bytes")

		if self.expected_hash is not None \
				and not hmac.compare_digest(
						self.hasher.digest(),
						self.expected_hash):
			raise SecurityError(
				"Blob has invalid hash (\"%s\" != \"%s\")"
				% (b64encode(self.hasher.digest()),
					b64encode(self.expected_hash)))

		if self.interval is not None:
			print(" %s (%s)" % (
				humanize_size(self.transferred_gross),
				humanize_duration(
					time.monotonic() - self.started)),
				end="", flush=True)

		if self.wrapped is not None:
			self.wrapped.close()

	# Return the number of bytes to pad the blob with according to the
	# Padme scheme (https://lbarman.ch/blog/padme).
	def padme(self, size: int) -> int:
		if size <= 64:
			# Pad small blobs to be 64 bytes at least.
			return 64 - size

		bit1 = size.bit_length() - 1
		bit2 = bit1.bit_length()

		more = 1 << (bit1 - bit2)
		mask = more - 1

		return (more - (size & mask)) & mask

	# Calculate a random amount of padding based on the covert scheme:
	# https://github.com/covert-encryption/covert/blob/main/docs/Specification.md#padding
	def covert(self, size: int) -> int:
		import math

		p = 0.05
		rnd1 = int.from_bytes(random.randbytes(4))
		rnd2 = int.from_bytes(random.randbytes(4))

		fixed_padding = max(0, int(p * 500) - size)
		eff_size = 200 + 1e8 * math.log(1 + 1e-8 * (size + fixed_padding))
		r = math.log(2**32) - math.log(rnd1 + rnd2 * 2**-32 + 2**-33)
		total_padding = fixed_padding + int(round(r * p * eff_size))

		return total_padding

	# Calculate the amount of padding based on the chosen method and the
	# net bytes (to be or already have been) transferred.
	def calc_padding(self, size: Optional[int] = None) -> int:
		if self.padding is None:
			return 0
		elif isinstance(self.padding, int):
			assert self.padding >= 0
			return self.padding

		assert size is not None
		if self.padding == self.Padding.PADME:
			return self.padme(size)
		elif self.padding == self.Padding.COVERT:
			return self.covert(size)
		else:
			assert False

	# We're called by the GCS library to provide data to upload.
	def read(self, n: Optional[int] = None) -> ByteString:
		assert self.wrapped is not None

		started = time.monotonic()
		self.check_progress(started)

		if self.expected_gross is None:
			# Haven't consumed @self.wrapped.
			buf = self.wrapped.read(n)
		else:	# May have consumed @self.wrapped.
			assert isinstance(self.padding, int)
			maxnet = self.expected_gross - self.padding
			if maxnet > self.transferred_gross:
				maxread = maxnet - self.transferred_gross
				buf = self.wrapped.read(min(n, maxread))
			else:	# We have consumed @self.wrapped.
				buf = bytearray()

		assert len(buf) <= n
		n -= len(buf)
		self.transferred_gross += len(buf)

		if n > 0 and self.padding:
			# Add padding to @buf.
			if not isinstance(self.padding, int):
				self.padding = self.calc_padding(
						self.transferred_gross)
				assert self.expected_gross is None
			if self.expected_gross is None:
				self.expected_gross = \
					self.transferred_gross + self.padding

			maxpad = self.expected_gross - self.transferred_gross
			padding = min(maxpad, n)

			assert self.csprng is not None
			buf += self.csprng.generate(padding)
			n -= padding
			self.transferred_gross += padding

		if self.hasher is not None:
			self.hasher.update(buf)

		if n > 0:
			# We have consumed @self.wrapped and/or
			# reached @self.expected_gross.
			assert self.expected_gross is None \
				or self.transferred_gross \
					== self.expected_gross

			# blob.upload_from_file() won't call us anymore,
			# so it's our only chance to call @self.final_cb().
			self.final_cb()

		self.delay(started)
		return buf

	# The GCS library is writing downloaded data to us.
	def write(self, buf: bytes) -> None:
		started = time.monotonic()
		self.check_progress(started)

		if self.expected_gross is not None:
			if self.transferred_gross + len(buf) \
					> self.expected_gross:
				# Server is sending more data
				# than the blob's nominal size.
				raise SecurityError(
					"Blob is larger than expected")

		if self.hasher is not None:
			self.hasher.update(buf)

		# @maxwrite := the maximum number of non-padding bytes
		# in @buf that need to be written to @self.wrapped.
		# Can be negative.
		if buf and self.padding:
			assert self.expected_gross is not None
			assert isinstance(self.padding, int)
			maxwrite = self.expected_gross - self.padding \
						- self.transferred_gross
		else:	# Empty @buf or no @self.padding.
			maxwrite = len(buf)

		padding = None
		if maxwrite >= len(buf):
			# Also covers len(@buf) == 0.
			if self.wrapped is not None:
				self.wrapped.write(buf)
		elif maxwrite > 0:
			# Part of @buf is padding, verify it.
			buf = memoryview(buf)
			if self.wrapped is not None:
				self.wrapped.write(buf[:maxwrite])
			padding = buf[maxwrite:]
		else:
			padding = buf

		if padding is not None:
			assert self.csprng is not None
			if (offset := self.csprng.verify(padding)) is not None:
				raise SecurityError(
					"Invalid padding at offset %d"
					% (self.transferred_gross + offset))

		self.transferred_gross += len(buf)
		self.delay(started)

	def tell(self) -> int:
		return self.transferred_gross
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

	_user_size: Optional[int] = None
	_user_size_incomplete: bool = False

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
			self._add("_user_size", what._user_size)
			self._user_size_incomplete |= \
					what._user_size_incomplete
		else:
			self._add("_blob_size", what.blob_size)
			self._add("_user_size", what.user_size)

	def _get(self, attr: str, none: bool = False, **kw) -> Optional[str]:
		value = getattr(self, attr)
		if value is None:
			if none:
				return None
			if not getattr(self, f"{attr}_incomplete"):
				return "???"
			value = 0

		value = humanize_size(value, **kw)
		if getattr(self, f"{attr}_incomplete"):
			value += '+'
		return value

	def blob_size(self, none: bool = False, **kw) -> Optional[str]:
		return self._get("_blob_size", none=none, **kw)

	def user_size(self, none: bool = False, **kw) -> Optional[str]:
		return self._get("_user_size", none=none, **kw)

	def get(self, **kw) -> str:
		sizes = [ self.blob_size(**kw) ]

		user_size = self.user_size(none=True, **kw)
		if user_size is not None:
			sizes.append(user_size)

		return '/'.join(sizes)
# }}}

# A chain of subprocesses.  When the Pipeline is deleted, its subprocesses
# are killed.
class Pipeline: # {{{
	# Allow it to be an int for subprocess.PIPE and DEVNULL.
	StdioType = Union[int, io.IOBase]

	# A subset of subprocess.Popen used by this class.
	class SubprocessIface(Protocol): # {{{
		pid: int
		returncode: Optional[int]

		stdin: Optional[io.IOBase]
		stdout: Optional[io.IOBase]
		stderr: Optional[io.IOBase]

		def kill(self) -> None:
			...

		def wait(self) -> int:
			...
		# }}}

	# An adaptor of multiprocessing.Process to SubprocessIface.
	class Subprocess(SubprocessIface): # {{{
		wrapped: multiprocessing.Process

		# Create a multiprocessing.Pipe and add it to the Subprocess
		# descriptor @cmd.
		@staticmethod
		def add_pipe(cmd: dict[str, Any], duplex=False) \
				-> tuple[
					multiprocessing.connection.Connection,
					multiprocessing.connection.Connection,
				]:
			conn_r, conn_w = multiprocessing.Pipe(duplex=duplex)

			# Close the reader side of the pipe in the child.
			assert "preexec_fn" not in cmd
			cmd["preexec_fn"] = lambda: conn_r.close()

			# Close the writer side in the parent after forking.
			assert "postexec_fn" not in cmd
			cmd["postexec_fn"] = lambda: conn_w.close()

			return conn_r, conn_w

		def __init__(self,
				executable: Callable[..., None],
				name: Optional[str] = None,
				args: Optional[Union[
					Sequence[Any],
					dict[str, Any],
				]] = None,
				env: Optional[dict[str, str]] = None,
				text: bool = False,
				stdin: Optional[StdioType] = None,
				stdout: Optional[StdioType] = None,
				stderr: Optional[StdioType] = None,
				preexec_fn: Optional[Callable[[], None]] = None,
			):
			read_mode = 'r' if text else "rb"
			write_mode = 'w' if text else "wb"

			if stdin == subprocess.PIPE:
				stdin_r, stdin_w = os.pipe()
			if stdout == subprocess.PIPE:
				stdout_r, stdout_w = os.pipe()
			if stderr == subprocess.PIPE:
				stderr_r, stderr_w = os.pipe()

			def fun():
				if stdin == subprocess.PIPE:
					os.close(stdin_w)
					sys.stdin = os.fdopen(stdin_r,
								read_mode)
				elif stdin == subprocess.DEVNULL:
					# @sys.stdin has been redirected to
					# /dev/null by the multiprocessing
					# module automatically.
					pass
				elif stdin is not None:
					assert isinstance(stdin, io.IOBase)
					sys.stdin = stdin
				if stdin is not None:
					# Make sure sys.stdin.fileno() is 0.
					os.dup2(sys.stdin.fileno(), 0)

				if stdout == subprocess.PIPE:
					os.close(stdout_r)
					sys.stdout = os.fdopen(stdout_w,
								write_mode)
				elif stdout == subprocess.DEVNULL:
					sys.stdout = open(os.devnull,
								write_mode)
				elif stdout is not None:
					assert isinstance(stdout, io.IOBase)
					sys.stdout = stdout
				if stdout is not None:
					os.dup2(sys.stdout.fileno(), 1)

				if stderr == subprocess.PIPE:
					os.close(stderr_r)
					sys.stderr = os.fdopen(stderr_w,
								write_mode)
				elif stderr == subprocess.DEVNULL:
					sys.stderr = open(os.devnull,
								write_mode)
				elif stderr == subprocess.STDOUT:
					sys.stderr = sys.stdout
				elif stderr is not None:
					assert isinstance(stderr, io.IOBase)
					sys.stderr = stderr
				if stderr is not None:
					os.dup2(sys.stderr.fileno(), 2)

				if env is not None:
					# Replacing @os.environ directly would
					# lose its magic.
					os.environ.clear()
					os.environ.update(env)

				if preexec_fn is not None:
					preexec_fn()

				if args is None:
					executable()
				elif isinstance(args, dict):
					executable(**args)
				else:
					executable(*args)

			if name is None:
				name = executable.__name__
			self.wrapped = multiprocessing.Process(target=fun,
								name=name)
			self.wrapped.start()

			if stdin == subprocess.PIPE:
				os.close(stdin_r)
				self.stdin = os.fdopen(stdin_w, write_mode)
			else:
				self.stdin = None

			if stdout == subprocess.PIPE:
				os.close(stdout_w)
				self.stdout = os.fdopen(stdout_r, read_mode)
			else:
				self.stdout = None

			if stderr == subprocess.PIPE:
				os.close(stderr_w)
				self.stderr = os.fdopen(stderr_r, read_mode)
			else:
				self.stderr = None

		@property
		def name(self) -> str:
			return self.wrapped.name

		@property
		def pid(self) -> int:
			return self.wrapped.pid

		@property
		def returncode(self) -> Optional[int]:
			return self.wrapped.exitcode

		def terminate(self) -> None:
			self.wrapped.terminate()

		def wait(self) -> int:
			self.wrapped.join()
			return self.wrapped.exitcode
		# }}}

	processes: list[SubprocessIface]

	_stdin: Optional[StdioType]
	_stdout: Optional[StdioType]

	def __init__(self,
			cmds: Sequence[Union[
				Callable[..., None],
				str, Sequence[str],
				dict[str, Any],
			]],
			stdin: Optional[StdioType] = subprocess.DEVNULL,
			stdout: Optional[StdioType] = None):
		if isinstance(stdin, int):
			assert stdin < 0
		if isinstance(stdout, int):
			assert stdout < 0

		self.processes = [ ]
		for i, cmd in enumerate(cmds):
			if callable(cmd):
				cmd = { "executable": cmd }
			elif not isinstance(cmd, dict):
				cmd = { "args": cmd }

			if isinstance(cmd.get("args"), str):
				cmd.setdefault("shell", True)

			if i > 0:
				cmd["stdin"] = self.processes[-1].stdout

				# Don't leak the pipeline's stdin,
				# because it can cause a deadlock.
				preexec = cmd.get("preexec_fn")
				def new_preexec() -> None:
					stdin = self.stdin()
					if stdin is not None:
						stdin.close()
					if preexec is not None:
						preexec()
				cmd["preexec_fn"] = new_preexec
			else:	# First process in the pipeline.
				cmd["stdin"] = stdin

			if i < len(cmds) - 1:
				cmd["stdout"] = subprocess.PIPE
			else:	# Last process in the pipeline.
				cmd["stdout"] = stdout

			postexec = cmd.pop("postexec_fn", None)
			if callable(cmd.get("executable")):
				proc = self.Subprocess(**cmd)
			else:
				proc = subprocess.Popen(**cmd)
			self.processes.append(proc)

			if i > 0:
				# Close the stdout of the previous process,
				# so it will receive a broken pipe if this
				# process dies.
				cmd["stdin"].close()

			if cmd.get("stderr") == subprocess.PIPE:
				cmd["stderr"] = proc.stderr

			if postexec is not None:
				postexec()

		self._stdin = stdin
		self._stdout = stdout
		if not self.processes \
				and stdin == subprocess.PIPE \
				and stdout == subprocess.PIPE:
			# This is deadlock-prone.
			stdin, stdout = os.pipe()
			self._stdin = os.fdopen(stdin, "rb")
			self._stdout = os.fdopen(stdout, "wb")

	def __del__(self):
		for proc in self.processes:
			try:
				proc.terminate()
				proc.wait()
			except:
				pass

	def __len__(self) -> int:
		return len(self.processes)

	def __getitem__(self, i: int) -> SubprocessIface:
		return self.processes[i]

	# Return a file that can be written to.
	def stdin(self) -> Optional[BinaryIO]:
		if self.processes:
			return self.processes[0].stdin
		elif self._stdout is subprocess.DEVNULL:
			return open(os.devnull, "wb")
		else:
			assert self._stdout is None \
				or isinstance(self._stdout, io.IOBase)
			return self._stdout

	# Return a file that can be read from.
	def stdout(self) -> Optional[BinaryIO]:
		if self.processes:
			return self.processes[-1].stdout
		elif self._stdin is subprocess.DEVNULL:
			return open(os.devnull, "b")
		else:
			assert self._stdin is None \
				or isinstance(self._stdin, io.IOBase)
			return self._stdin

	def wait(self) -> None:
		errors = [ ]
		for proc in self.processes:
			try:
				wait_proc(proc)
			except FatalError as ex:
				errors.append(ex)
		if errors:
			raise FatalError(", ".join(map(str, errors)))
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
				self.must_exist(self.escaped.sub(
						r"\1", pattern))
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

	def listdir(self, path: str) -> list[str]:
		return sorted(super().listdir(path))
# }}}

# A virtual file system.
class VirtualGlobber(Globber): # {{{
	@dataclasses.dataclass
	class DirEnt:
		globber: VirtualGlobber

		# '/' if the entry is the original VirtualGlobber.root,
		# or a single path component.
		fname: str

		# None if the entry is the original VirtualGlobber.root,
		# a PurePath of the entry's former parent if it was made
		# a root with make_root(), or the parent of a non-TLD.
		parent: Optional[Self | pathlib.PurePath] = None

		# Whether this entry has been committed to the globber.
		# If not, and the command that created it fails, it will be
		# removed from the tree.
		volatile: bool = False

		# Any associated object, eg. a MetaBlob.
		obj: Any = None

		@classmethod
		def mkroot(cls, globber: VirtualGlobber, obj: Any = None) \
				-> Self:
			return cls(globber, '/', obj=obj)

		@classmethod
		def mkdir(cls, globber: VirtualGlobber, fname: str,
				children: Optional[dict[str, Self]] = None,
				obj: Any = None, volatile: bool = False) \
				-> Self:
			self = cls(globber, fname, obj=obj, volatile=volatile)
			if children is not None:
				self.children = children
			return self

		@classmethod
		def mkfile(cls, globber: VirtualGlobber, fname: str,
				obj: Any = None, volatile: bool = False) \
				-> Self:
			self = cls(globber, fname, obj=obj, volatile=volatile)

			# Prevents the children() method from ever being called
			# and makes isdir() return False.
			self.children = None

			return self

		def __post_init__(self):
			if self.fname in ("", ".", ".."):
				raise ConsistencyError(
					"%s: invalid directory entry"
					% self.path())
			if self.volatile:
				self.globber.volatiles.add(self)

		@functools.cached_property
		def children(self) -> dict[str, Self]:
			# Set the property to avoid infinite recursion.
			self.children = { }
			try:
				self.globber.load_children(self)
			except:	# Retry when the property is read
				# the next time.
				delattr(self, "children")
				raise
			return self.children

		# For sorted() in __iter__().
		def __lt__(self, other: Self) -> bool:
			return self.fname < other.fname

		def __eq__(self, other: Self) -> bool:
			return id(self) == id(other)

		def __hash__(self) -> int:
			return id(self)

		def __repr__(self) -> str:
			parent = self.parent
			if isinstance(parent, __class__):
				parent = "..."
			children = "..." if self.isdir() else None

			return "%s(fname=%r, children=%s, parent=%s)" \
				% (self.__class__.__name__, self.fname,
					children, parent)

		# Return the DirEnt's path relative to another path,
		# or as an absolute path, either from the VirtualGlobber's
		# current @root or the original root if @full_path is True.
		def path(self, relative_to: Optional[Self] = None,
				full_path: bool = False) -> pathlib.PurePath:
			assert not full_path or relative_to is None

			prefix = CurDir
			dent, parts = self, [ ]
			while dent is not relative_to:
				if not dent.is_tld():
					parts.append(dent.fname)
					dent = dent.parent
					continue

				if relative_to is not None:
					this_path = self.path()
					other_path = relative_to.path()
					raise ValueError(
						"%s is not under %s"
						% (this.path, other_path))

				if dent.parent is None:
					parts.append(dent.fname)
					break

				assert isinstance(dent.parent,
							pathlib.PurePath)
				if full_path:
					parts.append(dent.fname)
					prefix = dent.parent
				else:
					prefix = RootDir
				break

			return prefix / pathlib.PurePath(*reversed(parts))

		# Turn this DirEnt into a directory.
		def make_dir(self) -> None:
			assert not self.isdir()
			self.children = { }

		# Turn this DirEnt into a top-level directory.
		def make_root(self) -> None:
			if self.parent is None:
				assert self.fname == '/'
			elif isinstance(self.parent, __class__):
				self.parent = self.parent.path(full_path=True)
			self.volatile = False

		# Whether @self.globber.load_children() or load_subtree()
		# has been called for this DirEnt.
		def children_loaded(self):
			return "children" in self.__dict__

		# Invalidate @self.children.
		def unload_children(self):
			assert self.isdir()
			if self.children_loaded():
				del self.children

		def isdir(self):
			# Need to be careful because @children is a cached
			# property.
			return not self.children_loaded() \
				or self.children is not None

		def must_be_dir(self) -> None:
			if not self.isdir():
				raise NotADirectoryError(self.path())

		# Returns whether the entry is the original VirtualGlobber.root
		# (@parent is None) or has been make_root().
		def is_tld(self) -> bool:
			return not isinstance(self.parent, __class__)

		# Returns whether the entry or one of its ancestors is @parent
		# up to the nearest TLD.
		def has_parent(self, parent: Self) -> bool:
			dent = self
			while True:
				if dent is parent:
					return True
				elif dent.is_tld():
					return False
				dent = dent.parent

		def __iter__(self) -> Iterator[Self]:
			assert self.isdir()
			return iter(sorted(self.children.values()))

		def __contains__(self, fname: str) -> bool:
			assert self.isdir()
			return fname in self.children

		def __getitem__(self, fname: str) -> Self:
			assert self.isdir()
			child = self.children.get(fname)
			if child is None:
				raise FileNotFoundError(self.path() / fname)
			return child

		def get(self, fname: str) -> Optional[Self]:
			assert self.isdir()
			return self.children.get(fname)

		def add(self, child: Self) -> Self:
			assert child.globber is self.globber
			assert child.fname != '/'
			assert child.parent is None
			assert self.isdir()

			if child.fname in self.children:
				raise FileExistsError(
					self.path() / child.fname)

			self.children[child.fname] = child
			child.parent = self

			return child

		def remove(self, child: Self) -> Self:
			assert self.isdir()
			del self.children[child.fname]
			child.parent = None
			return child

		def infanticide(self) -> None:
			assert self.isdir()
			for child in self:
				child.parent = None
			self.children = { }

		# children=False: add a file
		# children=True:  add a directory, children = { }
		# children=None:  add a directory, children are not loaded
		# children=dict:  add a directory, children = dict
		def add_child(self, fname: str,
				children: Union[bool, None, dict[str, Self]]
						= False,
				obj: Any = None, volatile: bool = False) \
				-> Self:
			if children is False:
				child = self.mkfile(
						self.globber, fname,
						obj=obj, volatile=volatile)
			else:
				if children is True:
					children = { }
				child = self.mkdir(
						self.globber, fname,
						children=children,
						obj=obj, volatile=volatile)
			return self.add(child)

		def ls(self) -> Iterable[str]:
			self.must_be_dir()
			return sorted(self.children.keys())

		def load_subtree(self) -> None:
			assert self.isdir()

			if not self.children_loaded():
				# Load all our descendents at once.
				self.children = { }
				self.globber.load_subtree(self)
				return

			# Make sure all our descendents are loaded as well.
			for child in self:
				if child.isdir():
					child.load_subtree()

		def scan(self, pre_order: Optional[bool] = True) \
				-> Iterator[Self]:
			if pre_order is True:
				yield self

			if self.isdir():
				self.load_subtree()
				for child in self:
					# It doesn't make sense to propagate
					# @pre_order if it's None.
					it = child.scan(pre_order is not False)
					yield from it

			if pre_order is False:
				yield self

		# Make the entry and its ancestors non-volatile.
		def commit(self, obj: Any = None) -> None:
			if obj is not None:
				self.obj = obj

			# We expect the root to be non-volatile.
			dent = self
			while dent.volatile:
				dent.volatile = False
				assert not dent.is_tld()
				dent = dent.parent

		# Remove this entry's branch if it's volatile.
		def rollback(self) -> None:
			if not self.volatile:
				return
			assert not self.is_tld()
			self.volatile = False

			child, parent = self, self.parent
			while parent.volatile:
				# Make sure we don't roll back @parent again
				# through a different path.  If we didn't,
				# the second time we'd find a volatile TLD,
				# failing the assertion below.
				parent.volatile = False
				assert not parent.is_tld()
				child, parent = parent, parent.parent
			parent.remove(child)

	root:		DirEnt
	cwd:		DirEnt

	# Uncommitted entries created by the currently executing command.
	volatiles:	set[DirEnt]

	def __init__(self, files: Iterable[Any] = ()):
		self.volatiles = set()
		self.cwd = self.root = self.DirEnt.mkroot(self)
		for file in files:
			self.add_file(pathlib.PurePath(str(file)), file)

	def add_file(self, path: pathlib.PurePath, obj: Any = None,
			is_dir: bool = False) -> DirEnt:
		parent = self.root
		start = 1 if path.is_absolute() else 0
		for fname in path.parts[start:-1]:
			child = parent.get(fname)
			if child is None:
				child = parent.add_child(fname, children=True)
			parent = child

		return parent.add_child(path.name, children=is_dir, obj=obj)

	# Called by DirEnt.children().
	def load_children(self, dent: DirEnt) -> None:
		pass

	# Called by DirEnt.scan().
	def load_subtree(self, dent: DirEnt) -> None:
		self.load_children(dent)

	def lookup(self, path: Union[str, pathlib.PurePath],
			create: Union[bool, Callable[[DirEnt], None]] = False
			) -> DirEnt:
		if isinstance(path, str):
			if not path:
				raise FileNotFoundError(path)
			must_be_dir = path.endswith(('/', "/."))
			path = pathlib.PurePath(path)
		else:
			must_be_dir = False

		if path.is_absolute():
			parts = path.parts[1:]
			dent = self.root
		else:
			parts = path.parts
			dent = self.cwd

		created = False
		for i, fname in enumerate(parts):
			dent.must_be_dir()
			if fname != "..":
				try:
					dent = dent[fname]
				except FileNotFoundError:
					if not create:
						raise

					parent = dent
					add_dir = i < len(parts) - 1 \
							or must_be_dir
					dent = parent.add_child(fname,
							children=add_dir,
							volatile=True)

					# Make rollback() more efficient
					# by having only the bottommost child
					# in @self.volatiles.
					self.volatiles.discard(dent.parent)
					self.volatiles.add(dent)

					if callable(create):
						create(dent)
					created = True
			elif created:
				# Refuse to create multiple directories by
				# looking up enoent-1/../enoent-2/../enoent-3.
				raise UserError(
					"%s: cannot reference the parent "
					"of a newly created directory"
					% path)
			elif not dent.is_tld():
				# @fname == "..", go one level up if we can.
				dent = dent.parent
		if must_be_dir:
			dent.must_be_dir()

		return dent

	def rollback(self) -> None:
		for dent in self.volatiles:
			dent.rollback()
		self.volatiles.clear()

	def chdir(self, path: Union[str, pathlib.PurePath],
			create: bool = False) -> None:
		dent = self.lookup(path, create)
		dent.must_be_dir()
		self.cwd = dent

	def chroot(self, path: Union[str, pathlib.PurePath],
			create: bool = False) -> None:
		dent = self.lookup(path, create)
		dent.must_be_dir()

		if not self.cwd.has_parent(dent):
			# @self.cwd is not under the new root.
			self.cwd = dent
		self.root = dent

		dent.make_root()

	def listdir(self, path: str) -> list[str]:
		return self.lookup(path).ls()

	def isdir(self, path: str) -> bool:
		return self.lookup(path).isdir()

	def islink(self, path: str) -> bool:
		return False

	def must_exist(self, path: str) -> None:
		self.lookup(path)

	def exists(self, path: str) -> bool:
		try:
			self.must_exist(path)
		except (FileNotFoundError, NotADirectoryError):
			return False
		else:
			return True

# A globber which supports incremental loading of blobs from a bucket.
class GCSGlobber(VirtualGlobber):
	args: EncryptedBucketOptions

	def __init__(self, args: EncryptedBucketOptions):
		super().__init__()
		self.args = args

	# Return a prefix that matches all blobs under @dent.
	def gcs_prefix(self, dent: VirtualGlobber.DirEnt) -> Optional[str]:
		return self.args.with_prefix(dent.path(full_path=True))

	def load_children(self, dent: VirtualGlobber.DirEnt) -> None:
		if self.args.encrypt_metadata:
			# Reconstruct the whole hierarchy from the files
			# directly under @dent.
			self.load_subtree(dent)
			return

		lst = self.args.bucket.list_blobs(
				prefix=self.gcs_prefix(dent),
				delimiter='/',
				include_folders_as_prefixes=True)
		for blob in lst:
			blob = MetaBlob.create_best_from_gcs(self.args, blob)
			if blob is not None:
				dent.add_child(blob.user_path.name, obj=blob)

		for prefix in lst.prefixes:
			# If we allowed these, we could create
			# a non-existent subdirectory.
			if prefix.endswith(("//", "/./")):
				raise ConsistencyError(
					"weird entry in %s (%s)"
					% (dent.path(), prefix))

			dent.add_child(pathlib.PurePath(prefix).name,
					children=None)

	def load_subtree(self, dent: VirtualGlobber.DirEnt) -> None:
		if self.args.encrypt_metadata:
			# We're expected to be called only once,
			# to load all the blobs directly under the
			# GCS prefix.
			assert dent == self.root
			assert dent.fname == '/'

		# Trim @root_path from @blob.user_path in case we've
		# changed root directory.
		root_path = self.root.path(full_path=True).relative_to(RootDir)
		prefix = self.gcs_prefix(dent)
		for blob in self.args.bucket.list_blobs(prefix=prefix):
			blob = MetaBlob.create_best_from_gcs(self.args, blob)
			if blob is None:
				continue

			self.add_file(blob.user_path.relative_to(root_path),
					blob)

		if self.args.encrypt_metadata or not self.args.is_hfs:
			return

		# Add the empty folders in the bucket.
		bucket_path = self.args.bucket_path()
		folders_path = f"{bucket_path}/folders/"
		req = google.cloud.storage_control_v2.ListFoldersRequest(
			parent=bucket_path, prefix=prefix)
		for folder in self.args.gcs_ctrl.list_folders(request=req):
			path = folder.name.removeprefix(folders_path)
			if path == prefix:
				continue
			path = self.args.without_prefix(path)

			try:
				self.add_file(
					pathlib.PurePath(path) \
						.relative_to(root_path),
					is_dir=True)
			except FileExistsError as ex:
				# @path must have been added implicitly
				# for a blob.
				assert self.lookup(ex.args[0]).isdir()
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

# I wonder what's the point of returning a base64 string as bytes.
def b64encode(v: ByteString) -> str:
	return base64.b64encode(v).decode()

# Wrapper around subprocess.check_output() that handles exceptions.
def subprocess_check_output(*args, **kwargs) -> bytes:
	try:
		return subprocess.check_output(*args, **kwargs)
	except subprocess.CalledProcessError as ex:
		# Conceal the arguments, they might be sensitive.
		ex.cmd = ex.cmd[0]
		raise FatalError from ex

# Write @comm to /proc/self/comm, shallowing exceptions.
def update_comm(comm: str) -> None:
	try:
		with open("/proc/self/comm", "w") as f:
			f.write(comm)
	except IOError:
		pass

# Wait for a subprocess and raise a FatalError if it exited with non-0 status.
def wait_proc(proc: Pipeline.SubprocessIface) -> None:
	# When we execute Python functions in separate processes, we use
	# update_comm() to identify what it is actually doing.
	try:
		comm = open("/proc/%d/comm" % proc.pid)
	except IOError:
		# Could be already reaped if we're called repeatedly.
		if isinstance(proc, subprocess.Popen):
			prog = proc.args[0]
		else:
			assert isinstance(proc, Pipeline.Subprocess)
			prog = proc.name
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
# Transfer data from @inp to @out as fast as possible, optionally writing
# the number of bytes transferred to the @counter.
def cat(inp: Optional[int] = None, out: Optional[int] = None,
		maxbytes: Optional[int] = None,
		counter: Optional[
				multiprocessing.connection.Connection
			] = None) -> None:
	update_comm("cat")

	if inp is None:
		inp = sys.stdin.fileno()
	if out is None:
		out = sys.stdout.fileno()

	# Try to increase the pipe buffers to the maximum.
	try:
		maxbuf = int(open("/proc/sys/fs/pipe-max-size").readline())
	except (OSError, ValueError):
		maxbuf = 1024*1024

	for fd in (inp, out):
		try: fcntl.fcntl(fd, fcntl.F_SETPIPE_SZ, maxbuf)
		except OSError: pass

	# splice(2) has been measured to be marginally faster than dd(1).
	total = 0
	while maxbytes is None or total < maxbytes:
		if maxbytes is None or maxbuf <= maxbytes - total:
			n = maxbuf
		else:
			n = maxbytes - total

		try:
			n = os.splice(inp, out, n)
		except OSError as ex:
			# @inp might not support splice()ing.
			if ex.errno != errno.EINVAL:
				raise

			buf = os.read(inp, n)
			os.write(out, buf)
			n = len(buf)

		if n <= 0:
			break
		total += n

		if maxbytes is not None:
			assert total <= maxbytes

	if counter is not None:
		counter.send(total)

# Write @blob.blob_uuid as binary to @sys.stdout, then optionally shovel
# stdin to stdout until EOF.
def write_external_encryption_header(blob: MetaBlob, then_cat: bool = False) \
		-> Callable[..., None]:
	def write_header(counter: Optional[
				multiprocessing.connection.Connection
			] = None) -> None:
		# Redirect this function's stdout to stderr, so it doesn't
		# go into the pipeline by accident.
		stdout, sys.stdout = sys.stdout, sys.stderr

		update_comm("write_header")

		try:
			os.write(
				stdout.fileno(),
				blob.external_header(blob.DataType.PAYLOAD))
			if then_cat:
				cat(out=stdout.fileno(), counter=counter)
		except Exception as ex:
			# The contents of exceptions are not passed back
			# to the main interpreter, so let's print it here.
			print(ex, file=sys.stderr)
			raise

	return write_header

def upload_blob(args: UploadBlobOptions, blob: MetaBlob,
		command: Optional[Sequence[str] | str] = None,
		pipeline_stdin: Optional[Pipeline.StdioType] = None,
		padding: Optional[Progressometer.Padding] = None,
		count_bytes_in: bool = True, wet_run: bool = False,
		overwrite: Optional[bool] = None) -> int:
	if command is None:
		assert pipeline_stdin is not None
		assert isinstance(pipeline_stdin, io.IOBase)
		pipeline_stdin_stat = os.stat(pipeline_stdin.fileno())
	else:
		pipeline_stdin_stat = None

	if args.encrypt_external() and args.add_header_to_blob:
		# Write @blob_uuid into the pipeline before the @command
		# is executed.  If we're using InternalEncrypt, it will add
		# the headers itself.
		if command is not None:
			command = {
				"args": command,
				"preexec_fn":
					write_external_encryption_header(blob),
			}
		else:
			command = {
				"name": "cat",
				"executable":
					write_external_encryption_header(
						blob, then_cat=True),
			}

	pipeline = [ ]
	if command is not None:
		pipeline.append(command)
	if args.compressor is not None:
		pipeline.append(args.compressor)
	if args.encrypt_external():
		pipeline.append(blob.external_encrypt())

	# If @pipeline is empty or it only contains @command, @bytes_in_counter
	# will be either InternalEncrypt or the Progressometer.  If @pipeline
	# is not empty but there's no @command we're uploading @pipeline_stdin.
	bytes_in_counter = None
	if pipeline and (command is None or len(pipeline) > 1) \
			and count_bytes_in:
		if command is not None:
			assert pipeline[0] is command
		if isinstance(command, dict) and "executable" in command:
			# @command will also count its output.
			assert command["name"] == "cat"
			bytes_in_counter = command
		elif command is not None:
			# Insert @bytes_in_counter right after @command
			# to count its output.
			bytes_in_counter = { }
			pipeline.insert(1, bytes_in_counter)
		elif not stat.S_ISREG(pipeline_stdin_stat.st_mode):
			# Insert @bytes_in_counter before anything else,
			# counting @pipeline_stdin.
			bytes_in_counter = { }
			pipeline.insert(0, bytes_in_counter)
		else:	# We know the file size already.
			bytes_in_counter = pipeline_stdin_stat.st_size

		if isinstance(bytes_in_counter, dict):
			# Create a pipe through which @bytes_in_counter
			# can tell us the number of bytes transferred.
			counter_r, counter_w = \
				Pipeline.Subprocess.add_pipe(bytes_in_counter)

			if "executable" not in bytes_in_counter:
				bytes_in_counter["executable"] = cat

			assert "args" not in bytes_in_counter
			bytes_in_counter["args"] = { "counter": counter_w }

			# @bytes_in_counter is in the @pipeline already.
			bytes_in_counter = counter_r

	# @pipeline could be empty.
	kw = { "stdout": subprocess.PIPE }
	if pipeline_stdin is not None:
		kw["stdin"] = pipeline_stdin
	pipeline = Pipeline(pipeline, **kw)

	src = pipeline.stdout()
	if args.encrypt_internal():
		src = blob.internal_encrypt(blob.DataType.PAYLOAD, src)
		if count_bytes_in and bytes_in_counter is None:
			bytes_in_counter = src

	# We know the @expected_bytes to transfer if @src is a regular file.
	if src is pipeline_stdin and stat.S_ISREG(pipeline_stdin_stat.st_mode):
		expected_bytes = pipeline_stdin_stat.st_size
	else:
		expected_bytes = None

	# Check the @pipeline for errors before returning the last read
	# to upload_from_file().  If pipeline.wait() throws an exception
	# the upload will fail and not create the blob.
	src = Progressometer(src, args.progress,
				autolag=args.laggy,
				final_cb=pipeline.wait,
				expected_net=expected_bytes, padding=padding,
				hashing=args.integrity >= args.Integrity.HASH)
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
					% blob.blob_name) from ex
			elif overwrite is False:
				raise ConsistencyError(
					"%s already exists in bucket"
					% blob.blob_name) from ex
			else:
				raise
		except GoogleAPICallError as ex:
			raise FatalError from ex
	else:	# In case of --wet-run just read @src until we hit EOF.
		if overwrite is not None:
			exists = blob.gcs_blob.bucket \
					.get_blob(blob.blob_name) is not None
			if exists and not overwrite:
				raise ConsistencyError(
					"%s already exists in bucket"
					% blob.blob_name)
			elif overwrite and not exists:
				raise ConsistencyError(
					"%s does not exist in bucket"
					% blob.blob_name)
		while src.read(1024*1024):
			pass

	src.final_progress()

	if not wet_run and blob.gcs_blob.size != src.transferred_gross:
		# GCS has a different idea about the blob's size than us.
		try:
			blob.gcs_blob.delete()
		except:	# We may not have permission to do so.
			print(f"WARNING: {blob.blob_name} could be corrupted, "
				"but unable to delete it!", file=sys.stderr)
		raise ConsistencyError(
				"Blob size mismatch (%d != %d)"
				% (blob.gcs_blob.size, src.transferred_gross))

	if bytes_in_counter is not None:
		if isinstance(bytes_in_counter, Progressometer):
			bytes_in = bytes_in_counter.transferred_gross
		elif isinstance(bytes_in_counter, InternalEncrypt):
			bytes_in = bytes_in_counter.bytes_in
		elif isinstance(bytes_in_counter, int):
			bytes_in = bytes_in_counter
		else:	# This is written by cat().
			assert isinstance(bytes_in_counter,
				multiprocessing.connection.Connection)
			bytes_in = bytes_in_counter.recv()
			assert isinstance(bytes_in, int)

			# Discount the header written by write_header().
			if isinstance(command, dict) \
					and "executable" not in command:
				header = blob.external_header(
						blob.DataType.PAYLOAD)
				assert bytes_in >= len(header)
				bytes_in -= len(header)
		blob.user_size = bytes_in

	if padding is not None:
		assert isinstance(src.padding, int)
		assert src.csprng is not None
		blob.padding = src.padding
		blob.padding_seed = src.csprng.seed

	if args.integrity >= args.Integrity.HASH:
		blob.blob_hash = src.hasher.digest()

	if (bytes_in_counter is not None \
				or src.padding \
				or args.integrity >= args.Integrity.SIZE) \
			and not wet_run:
		# In case of failure the blob won't be usable without
		# --integrity none, so it's okay not to delete it.
		blob.sync_metadata()

	return src.transferred_gross

# Read blob.external_header_st from the standard input and verify that it
# belogs to @blob, then either exec(@then_exec) or forward the remaining
# stdin to stdout.
def verify_external_encryption_header(blob: MetaBlob,
		then_exec: Optional[Sequence[str]] = None) -> None:
	update_comm("verify_header")

	# Read and parse the @header.
	header = os.read(sys.stdin.fileno(), blob.external_header_st.size)
	if len(header) < blob.external_header_st.size:
		sys.exit("Failed to read encryption header, only got %d bytes."
				% len(header))
	recv_uuid, recv_data_type = blob.external_header_st.unpack_from(header)

	# Verify the @header.
	if recv_data_type != blob.DataType.PAYLOAD.value:
		sys.exit("Data type ID (0x%.2X) differs from expected (0x%.2X)."
				% (recv_data_type, blob.DataType.PAYLOAD.value))
	if recv_uuid != blob.blob_uuid.bytes:
		sys.exit("Blob UUID (%s) differs from expected (%s)."
				% (uuid.UUID(bytes=recv_uuid), blob.blob_uuid))

	if then_exec is not None:
		os.execvp(then_exec[0], then_exec)
	else:
		cat()

def download_blob(args: DownloadBlobOptions, blob: MetaBlob,
		command: Union[None, Sequence[str], dict[str, Any]] = None,
		pipeline_stdout: Optional[Pipeline.StdioType] = None,
		pipeline_callback:
			Optional[Callable[[Pipeline], None]] = None) -> int:
	assert command is not None or pipeline_stdout is not None

	if args.encrypt_external() and args.add_header_to_blob:
		if command is None:
			command = { "name": "cat" }
		else:	# We can't use subprocess.Popen() with preexec_fn
			# because Popen() doesn't return before preexec_fn
			# finishes, so there'd a deadlock.
			if isinstance(command, dict):
				prog = command.pop("args")
			else:
				prog, command = command, { }

			command["name"] = prog[0]
			command["args"] = { "then_exec": prog }

		command["executable"] = verify_external_encryption_header
		command.setdefault("args", { })["blob"] = blob

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

	dst = Progressometer(dst, args.progress,
				autolag=args.laggy,
				expected_gross=blob.gcs_blob.size,
				padding=blob.padding,
				padding_seed=blob.padding_seed,
				hashing=blob.blob_hash)

	try:	# The actual download.
		blob.gcs_blob.download_to_file(dst, **args.get_retry_flags())
		dst.final_progress()
	except GoogleAPICallError as ex:
		raise FatalError from ex
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
	assert dst.transferred_gross == blob.gcs_blob.size
	return dst.transferred_gross
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
	for blob in args.bucket.list_blobs(prefix=args.with_prefix(RootDir)):
		blob = BackupBlob.create_from_gcs(args, blob)
		if blob is None:
			continue

		try:
			backup = by_uuid[blob.snapshot_uuid]
		except KeyError:
			backup = Backup(blob)
			existing = by_name.get(backup.snapshot_name)
			if existing is not None:
				raise ConsistencyError(
					"%s and %s have different UUIDs, "
					"but conflicting snapshot names"
					% (blob.blob_name, existing))
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
		raise UserError('\n'.join(errors))

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

		section = self.sections["operation"]
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
				mtime = blob.user_mtime.timestamp()
				print("", blob.payload_type.field(),
					time.strftime(
						"%Y-%m-%d %H:%M:%S",
						time.localtime(mtime)),
					SizeAccumulator(blob).get(),
					args.without_prefix(blob.blob_name),
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

		section = self.sections["deletion"]
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
			else:
				print(f"Deleting {blob} ({details})...")
				blob.gcs_blob.delete()

			backup.clear_blob(blob)

		# Delete @backup.index if we've deleted all backups.
		if ndeleted > prev_ndeleted and backup.orphaned():
			if backup.index is not None:
				blob = backup.index
				deleted_bytes += blob.gcs_blob.size

				if args.dry_run:
					print(f"Would delete {blob}.")
				else:
					print(f"Deleting {blob}...")
					blob.gcs_blob.delete()

			if not args.dry_run:
				args.delete_folder(args.with_prefix(
							backup.snapshot_name))

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
			mtime = backup.index.user_mtime.timestamp()
			print("",
				time.strftime(
					"%Y-%m-%d %H:%M:%S",
					time.localtime(mtime)),
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
			file=sys.stderr if args.output is None else sys.stdout)
		return

	output_dir = output = None
	if args.output is not None:
		print("Retrieving the index of:")
		for i in to_retrieve:
			print(f"  {backups[i]}")
		print()

		try:
			output = open(args.output, 'wb')
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
				output = open(output_path, 'wb')

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

		if backup.orphaned():
			args.delete_folder(args.with_prefix(
						backup.snapshot_name))

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
		section.add_disable_flag_no_dflt("--no-store-snapshot-size")

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

		self.merge_options_from_ini(args, "store_snapshot_size", tpe=bool)
		if args.store_snapshot_size is not None:
			self.store_snapshot_size = args.store_snapshot_size

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
	elif args.compressor is None:
		btrfs_send = (*btrfs_send, "--compressed-data")
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
		ret = upload_snapshot(args, blob, cmd)

		if backup is None:
			backups.add(Backup(blob))
		elif backup.full is None:
			backup.add_blob(blob)

		return ret
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
		ret = upload_snapshot(args, blob, cmd)

		if backup is None:
			backups.add(Backup(blob))
		elif backup.delta is None:
			backup.add_blob(blob)

		return ret
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
		if not (should_upload_full or should_upload_delta):
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

def download_backup(args: CmdDownload,
			fname: str, blob: BackupBlob,
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
	def local(self) -> Globber:
		assert isinstance(self, CmdFTP)
		return Globber()

	@functools.cached_property
	def remote(self) -> GCSGlobber:
		assert isinstance(self, CmdFTP)

		remote = GCSGlobber(self)
		if self.chdir is not None:
			remote.chdir(self.chdir)
		elif self.chroot is not None:
			remote.chroot(self.chroot)
		return remote

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

	load_all_blobs:	bool = False # XXX unfinished (dynamic discovery)
	chdir:		Optional[str] = None
	chroot:		Optional[str] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["bucket"]
		section.add_enable_flag_no_dflt("--load-all-blobs")

		section = self.sections["operation"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_argument("--chdir")
		mutex.add_argument("--chroot")

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args, "load_all_blobs", tpe=bool)
		if self.encrypt_metadata:
			# Blob names aren't arranged hierarchically,
			# we can't load them incrementally.
			self.load_all_blobs = True
		elif args.load_all_blobs is not None:
			self.load_all_blobs = args.load_all_blobs

		self.chdir = args.chdir
		self.chroot = args.chroot

	@functools.cached_property
	def subcommands(self) -> Sequence[CmdLineCommand]:
		return (CmdFTPTree(self), CmdFTPDir(self), CmdFTPDu(self),
			CmdFTPMkDir(self), CmdFTPRmDir(self),
			CmdFTPRm(self), CmdFTPMove(self),
			CmdFTPCat(self), CmdFTPPage(self),
			CmdFTPGet(self), CmdFTPPut(self), CmdFTPTouch(self))

	# Like shlex.split(), split a line of input into tokens,
	# paying attention to quotation and escaping.
	def split(self, s: str) -> Iterable[str]:
		token = None
		quoted = None
		escaped = False
		environ = environ_delimited = None
		for c in s:
			if environ is not None:
				assert not escaped

				isalnum = re.match(r'\w', c)
				if isalnum:
					environ += c
				elif not environ and c == '{':
					assert not environ_delimited
					environ_delimited = True
				elif environ_delimited and c != '}':
					raise ValueError(
						"%s: illegal character in "
						"environment variable name"
						% repr(c))
				elif not environ:
					raise ValueError(
						"Empty environment variable "
						"name")
				else:
					val = os.environ.get(environ)
					if val is None:
						raise ValueError(
							f"{environ}: no such "
							"environment variable")

					if token is None:
						token = val
					else:
						token += val
					environ = None

				if isalnum or environ_delimited:
					continue

			if escaped:
				assert token is not None
				if c == '\\' or c in Globber.GLOBBING:
					token += rf'\{c}'
				else:
					token += c
				escaped = False
			elif c == '$' and quoted != "'":
				environ = ""
				environ_delimited = False
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
			elif c == '#':
				break
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

		if environ is not None:
			if environ_delimited:
				raise ValueError(
					f"{environ}: unfinished environment "
					"variable name")
			elif not environ:
				raise ValueError(
					"Empty environment variable name")

			val = os.environ.get(environ)
			if val is None:
				raise ValueError(
					f"{environ}: no such environment "
					"variable")

			if token is None:
				token = val
			else:
				token += val

		if token is not None:
			yield token

	def execute(self) -> None:
		if self.interactive:
			import readline
			print("Operating on", self.bucket_with_prefix())

		error = False
		re_shell = re.compile(r"^\s*!(.*)")
		while True:
			# Setting the environment variable may leak memory,
			# so only do that if @error has changed.
			error_str = str(int(error))
			if os.environ.get("STATUS") != error_str:
				os.environ["STATUS"] = error_str

			try:
				if self.interactive:
					line = input(
						"%s> "
						% self.remote.cwd.path())
				else:
					line = input()
			except KeyboardInterrupt:
				print()
				continue
			except EOFError:
				if self.interactive:
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

			if not cmdline:
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
			finally:
				self.remote.rollback()

		if error:
			sys.exit(1)

# Execute the appropriate subcommand in the FTP shell.
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
			# The hack above is not desired for the subparsers of
			# the subparsers (the usage would omit the mid-level
			# subcommands).
			parent = CmdFTPShell.ArgumentParserNoUsage
			return super().add_subparsers(*args, **kw,
							parser_class=parent)

	# Remove the flags we don't want the @subcommands to have.
	# TODO: currently unused
	def prune(self, subcommands: Iterable[CmdLineCommand]) -> None:
		for cmd in subcommands:
			cmd.remove_argument("--debug")
			self.prune(cmd.subcommands)

	@functools.cached_property
	def subcommands(self) -> Sequence[CmdLineCommand]:
		subcommands = (CmdFTPHelp(self), CmdFTPExit(self),
				CmdFTPEcho(self), CmdFTPSetEnv(self),
				CmdFTPLChDir(self), CmdFTPLPwd(self),
				CmdFTPChDir(self), CmdFTPPwd(self),
				CmdFTPPushD(self), CmdFTPPopD(self),
				CmdFTPDirStack(self), CmdFTPTree(self),
				CmdFTPDir(self), CmdFTPPDir(self),
				CmdFTPDu(self),
				CmdFTPMkDir(self), CmdFTPRmDir(self),
				CmdFTPRm(self), CmdFTPMove(self),
				CmdFTPCat(self), CmdFTPPage(self),
				CmdFTPGet(self), CmdFTPPut(self),
				CmdFTPTouch(self))
		return subcommands

class FTPOverwriteOptions(CmdLineOptions):
	class IfExists(Choices, enum.Enum):
		FAIL		= enum.auto()
		SKIP		= enum.auto()
		ASK		= enum.auto()
		OVERWRITE	= enum.auto()

	if_exists: IfExists = IfExists.FAIL

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["force"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag("--no-clobber", "-n")
		mutex.add_enable_flag("--interactive", "-i")
		mutex.add_enable_flag("--force", "-f")
		mutex.add_argument("--exists",
			choices=self.IfExists.to_choices())

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		if args.no_clobber:
			self.if_exists = self.IfExists.SKIP
		elif args.interactive:
			self.if_exists = self.IfExists.ASK
		elif args.force:
			self.if_exists = self.IfExists.OVERWRITE
		elif args.exists is not None:
			self.if_exists = self.IfExists.from_choice(args.exists)

		# Make sure confirm() is not called when we're not interactive.
		if self.if_exists == self.IfExists.ASK \
				and not self.interactive:
			self.if_exists = self.IfExists.FAIL

	# Return whether the answer is affirmative and whether to apply it
	# always or raise SystemExit.
	def confirm(self, prompt: str) -> tuple[bool, bool]:
		import readline

		assert self.interactive
		n = readline.get_current_history_length()
		while True:
			try:
				ret = input("%s [Yes/Always/No/neVer/Quit] "
						% prompt)
			except EOFError:
				print()
				ret = None
			else:	# Remove this interaction from the history.
				# (If the user recalled an earlier input,
				#  no new entry was added to the history.)
				if readline.get_current_history_length() > n:
					readline.remove_history_item(n)
				ret = ret.lower()

			if ret in ('y', "yes"):
				return True, False
			elif ret in ('a', "always"):
				return True, True
			elif ret in ('n', "no"):
				return False, False
			elif ret in ('v', "never"):
				return False, True
			elif ret in ('q', "quit"):
				raise SystemExit(0)
			else:
				prompt = prompt.lstrip()

	# Return OVERWRITE, SKIP or FAIL, or raise SystemExit.
	def file_exists(self,
			dst: pathlib.PurePath,
			src: Optional[pathlib.PurePath] = None,
			prompt: Optional[str] = None) -> IfExists:
		if prompt is None:
			prompt = "%r exists" % str(dst)

		if self.if_exists == self.IfExists.ASK:
			prompt += ", overwrite"
			if src is not None:
				prompt += " with %r" % str(src)
			prompt += '?'

			agree, always = self.confirm(prompt)
			if agree:
				ret = self.IfExists.OVERWRITE
			else:
				ret = self.IfExists.SKIP
			if always:
				self.if_exists = ret

			return ret

		if self.if_exists == self.IfExists.SKIP:
			print(f"{prompt}, skipping.")
		return self.if_exists

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

class CmdFTPEcho(CmdExec):
	cmd = "echo"
	help = "TODO"

	what: list[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("what", nargs='*')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.what = args.what

	def execute(self):
		print(*self.what, sep=' ')

class CmdFTPSetEnv(CmdExec):
	cmd = "setenv"
	help = "TODO"

	name:  str
	value: str

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("environment")
		self.sections["positional"].add_argument("value")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.name = args.environment
		self.value = args.value

	def execute(self):
		os.environ[self.name] = self.value

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
		try:
			os.chdir(self.local.glob(os.path.expanduser(self.dst),
							at_least_one=True,
							at_most_one=True))
		except OSError as ex:
			raise FatalError from ex

class CmdFTPLPwd(CmdExec):
	cmd = "lpwd"
	help = "TODO"

	def execute(self):
		print(os.getcwd())

class CmdFTPChDir(CmdExec):
	cmd = "cd"
	help = "TODO"

	dst: str

	# Class variable to keep state.
	prev: Optional[str] = None

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("directory")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.dst = args.directory

	def chdir_path(self, path: str) -> str:
		cwd = self.remote.cwd.path()
		self.remote.chdir(path)
		self.__class__.prev = cwd
		return cwd

	def chdir_dst(self, dst: str) -> str:
		if dst != '-':
			return self.chdir_path(self.remote.glob(
						dst,
						at_least_one=True,
						at_most_one=True))
		elif self.prev is not None:
			return self.chdir_path(self.prev)
		else:
			raise UserError("No previous directory")

	def execute(self: _CmdFTPChDir):
		self.chdir_dst(self.dst)

class CmdFTPPwd(CmdExec):
	cmd = "pwd"
	help = "TODO"

	print_bucket: bool

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["operation"].add_enable_flag("--bucket", "-b")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.print_bucket = args.bucket

	def execute(self: _CmdFTPPwd):
		if self.print_bucket:
			print(self.bucket_with_prefix())
		else:
			print(self.remote.cwd.path())

class CmdFTPDirStack(CmdExec):
	cmd = "dirs"
	help = "TODO"

	clear: bool

	# Class variable to keep state.
	stack: list[str] = [ ]

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["operation"].add_enable_flag("--clear", "-c")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.clear = args.clear

	def pushd(self, dst: Optional[str]) -> None:
		if dst is not None:
			chdir = self.parent.find_subcommand("cd")
			self.stack.append(chdir.chdir_dst(dst))
		else:
			self.stack.append(self.remote.cwd.path())

	def popd(self) -> None:
		if not self.stack:
			raise UserError("Directory stack empty")

		chdir = self.parent.find_subcommand("cd")
		chdir.chdir_path(self.stack[-1])
		del self.stack[-1]

	def execute(self: _CmdFTPDirStack):
		if self.clear:
			self.stack.clear()
			return
		if self.stack:
			print(*self.stack, sep="\n")

class CmdFTPPushD(CmdExec):
	cmd = "pushd"
	help = "TODO"

	dst: Optional[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("directory", nargs='?')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.dst = args.directory

	def execute(self: _CmdFTPPushD):
		self.parent.find_subcommand("dirs").pushd(self.dst)

class CmdFTPPopD(CmdExec):
	cmd = "popd"
	help = "TODO"

	def execute(self: _CmdFTPPopD):
		self.parent.find_subcommand("dirs").popd()

class CmdFTPTree(CmdExec):
	cmd = "tree"
	help = "TODO"

	with_files:	bool
	with_hidden:	bool
	root:		Optional[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["operation"].add_enable_flag("--files", "-f")
		self.sections["operation"].add_enable_flag("--hidden", "-a")
		self.sections["positional"].add_argument("root", nargs='?')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.with_files = args.files
		self.with_hidden = args.hidden
		self.root = args.root

	def print_subtree(self, dent: VirtualGlobber.DirEnt, \
				*parents: tuple[bool]):
		line = [ ]
		if parents:
			for has_next in parents[:-1]:
				line.append('│' if has_next else ' ')
			line.append('├' if parents[-1] else '└')
		if dent.is_tld():
			line.append('/')
		elif dent.isdir():
			line.append(dent.fname + '/')
		else:
			line.append(dent.fname)
		print(*line, sep=' ')

		if not dent.isdir():
			return

		if not (self.with_files and self.with_hidden):
			# Collect the list of @children to show in advance
			# because we'll need to know which is the last one.
			children = [ ]
			for child in dent:
				if not self.with_files and not child.isdir():
					continue
				if not self.with_hidden:
					if child.fname.startswith('.'):
						continue
				children.append(child)
			nchildren = len(children)
		else:	# We're showing all children.
			children, nchildren = dent, len(dent.children)

		for i, child in enumerate(children):
			self.print_subtree(child, *parents, i < nchildren - 1)

	def execute(self: _CmdFTPTree):
		if self.root is not None:
			dent = self.remote.lookup(
					self.remote.glob(
						self.root,
						at_least_one=True,
						at_most_one=True))
		else:
			dent = self.remote.cwd
		if dent.isdir():
			dent.load_subtree()
		self.print_subtree(dent)

class CmdFTPDir(CmdExec):
	cmd = ("dir", "ls")
	help = "TODO"

	all:		bool
	ctime:		bool
	readdir:	bool
	recursive:	bool
	what:		list[str]

	# Overridden by CmdFTPPDir.
	output: TextIO = sys.stdout

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["operation"]
		section.add_enable_flag("--all", "-a")
		section.add_enable_flag("--ctime", "-c")
		section.add_enable_flag("--directory", "-d")
		section.add_enable_flag("--recursive", "-R")

		self.sections["positional"].add_argument("what", nargs='*')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.all = args.all
		self.ctime = args.ctime
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
				t = dent.obj.gcs_blob.time_created \
					if self.ctime \
					else dent.obj.user_mtime
				line.append(time.strftime(
						"%Y-%m-%d %H:%M:%S",
						time.localtime(t.timestamp())))
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
				line.append(size.user_size(with_exact=True))

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

		self.print_files(
			(child.fname, child) for child in dent
			if self.all or not child.fname.startswith('.'))

		if not self.recursive:
			return

		for child in dent:
			if not child.isdir():
				continue
			elif not self.all and child.fname.startswith('.'):
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
			if self.recursive and dent.isdir():
				dent.load_subtree()
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
					size.user_size(with_exact=True),
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

class CmdFTPMkDir(CmdExec):
	cmd = "mkdir"
	help = "TODO"

	what: list[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("what", nargs='+')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.what = args.what

	def execute(self: _CmdFTPMkDir) -> None:
		# It doesn't make a lot of sense to specify a pattern for this
		# command, but let's accept them anyway, so we behave like a
		# real shell (ie. "mkdir */xxx" won't do what the user might
		# expect, but it will err out instead of creating a directory
		# named "*/xxx").
		for path in self.remote.globs(self.what, must_exist=False):
			# If @path is empty, leave it so, making "mkdir ''"
			# an error.
			if path:
				# Make sure that self.remote.lookup()
				# creates a directory in the end.
				path += '/'

			dent = self.remote.lookup(path, create=True)
			if dent.volatile:
				print("Creating %s..." % dent.path())

				# @folder_id can only be None if @dent is the
				# @RootDir (and there's no @self.args.prefix),
				# but it can't be because @dent shouldn't exist
				# in GCS yet.
				folder_id = self.remote.gcs_prefix(dent)
				assert folder_id is not None

				self.create_folder(folder_id)
				dent.commit()

class CmdFTPRmDir(CmdExec):
	cmd = "rmdir"
	help = "TODO"

	what: list[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()
		self.sections["positional"].add_argument("what", nargs='+')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)
		self.what = args.what

	def execute(self: _CmdFTPRmDir) -> None:
		for match in self.remote.globs(self.what):
			dent = self.remote.lookup(match)
			if not dent.isdir():
				raise NotADirectoryError(match)
			elif dent.children:
				raise UserError(
					"%s: directory not empty"
					% dent.path())
			elif dent is self.remote.root:
				raise UserError(
					"Cannot delete the root directory")

			self.delete_folder(self.remote.gcs_prefix(dent))
			if dent is self.remote.cwd:
				self.remote.cwd = dent.parent
			dent.parent.remove(dent)

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

	def execute(self: _CmdFTPRm) -> None:
		# @to_delete := list of DirEnt:s to delete
		to_delete = [ ]
		for match in self.remote.globs(self.what):
			dent = self.remote.lookup(match)
			if not self.recursive and dent.isdir():
				raise IsADirectoryError(match)
			to_delete.append(dent)

		ndirs = nfiles = size = 0
		for top in to_delete:
			# Skip subtree if @top has been @deleted by an earlier
			# @to_delete.
			if not top.has_parent(self.remote.root):
				continue

			# Deleted DirEnt:s will be removed from the tree
			# after scan()ning it.  We also keep a list in case
			# there's an error.
			deleted = [ ]
			for dent in top.scan(pre_order=False):
				# Silently skip the root directory.
				if dent is self.remote.root:
					continue

				print("Deleting %s..." % dent.path())
				try:
					if dent.isdir():
						folder_id = self.remote \
							.gcs_prefix(dent)
						self.delete_folder(folder_id)
						ndirs += 1
					else:
						assert dent.obj is not None
						dent.obj.gcs_blob.delete()
						size += dent.obj.gcs_blob.size
						nfiles += 1
				except:	# Remove the @deleted DirEnt:s
					# from the tree.
					for dent in deleted:
						if self.remote.cwd is dent:
							# If @dent.parent is
							# also deleted, we'll
							# move @cwd once again
							# because @deleted is
							# in deletion order.
							self.remote.cwd = \
								dent.parent
						dent.parent.remove(dent)
					raise
				else:
					deleted.append(dent)

			if top is self.remote.root:
				# rm -rf /
				self.remote.cwd = top
				self.remote.root.infanticide()
			else:
				if top.isdir() and self.remote.cwd \
							.has_parent(top):
					# @cwd is or is under @top,
					# move it to @top's parent.
					self.remote.cwd = top.parent
				top.parent.remove(top)

		if self.verbose and (ndirs > 0 or nfiles > 0):
			print()
			print("Deleted %d directories and %d file(s) of %s."
				% (ndirs, nfiles, humanize_size(size)))

class CmdFTPMove(CmdExec, FTPOverwriteOptions):
	cmd = "mv"
	help = "TODO"

	if_exists = FTPOverwriteOptions.IfExists.ASK

	src: list[str]
	dst: str

	def declare_arguments(self) -> None:
		super().declare_arguments()

		self.sections["positional"].add_argument("what", nargs='+')
		self.sections["positional"].add_argument("where")

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.src = args.what
		self.dst = args.where

	def execute(self: _CmdFTPMove) -> None:
		srcs = list(map(self.remote.lookup,
				self.remote.globs(self.src)))
		dst_top = self.remote.lookup(
				self.remote.glob(self.dst,
						at_least_one=True,
						at_most_one=True,
						must_exist=False),
				create=True)

		# @move_src_top := move @src_top inside @dst_top
		# If False, just rename @src_top to @dst_top.
		move_src_top = dst_top.isdir()
		if not dst_top.isdir():
			if len(srcs) > 1:
				raise NotADirectoryError(dst_top.path())
			elif not srcs[0].isdir():
				# mv file <a-file> => OK (overwrite <a-file>)
				# mv file <enoent> => OK (rename file)
				pass
			elif not dst_top.volatile:
				# mv dir <a-file> => NOK
				raise NotADirectoryError(dst_top.path())
			else:	# mv dir <enoent> => OK
				dst_top.make_dir()

		# Pre-validate that none of the @srcs is a parent of another
		# coming after it, and that @dst_top is not a descendant of
		# @srcs.  This makes `mv src src/dir' and `mv src src/dir dst'
		# invalid.
		for i, src in enumerate(srcs):
			for other in srcs[i+1:]:
				if src == other:
					raise UserError(
						"%s is specified "
						"more than once"
						% src.path())
				elif other.has_parent(src):
					raise UserError(
						"%s is a parent of %s"
						% (src.path(), other.path()))

			if src == dst_top or src.parent == dst_top:
				# "mv <thing> <thing>" or "mv <thing> ."
				# Just skip it.
				srcs[i] = None
			elif dst_top.has_parent(src):
				raise UserError(
					"%s is a parent of %s"
					% (src.path(), dst_top.path()))
		srcs = [ src for src in srcs if src is not None ]

		movemap = { }
		for src_top in srcs:
			self.map_moves(movemap, src_top, dst_top, move_src_top)

		try:
			uncommitted = [ ]
			for src_top in srcs:
				self.exec_moves(movemap, uncommitted, src_top)
		except:	# Roll back the @uncommitted changes.
			for dent, old_user_path in uncommitted:
				try:
					blob = dent.obj
					blob.user_path = old_user_path
					blob.sync_metadata(update_mtime=False)
				except:	# Don't let this error interrupt the
					# rollback of the rest of the @dent:s.
					CmdTop.print_exception()
			raise
		else:	# No errors, all changes must have been committed.
			assert not uncommitted

	# Walk through @src and return where to move what in @movemap,
	# taking into account what would be overwritten and what should be
	# skipped.
	def map_moves(self, movemap: dict[VirtualGlobber.DirEnt,
						VirtualGlobber.DirEnt],
			src: DirEnt, dst: DirEnt, add_child: bool = True) \
			-> None:
		if src in movemap:
			# File has already been moved through a different
			# src_top, as in "mv <src>/<file> <src> <dst>".
			return

		if add_child:
			child = dst.get(src.fname)
			child_existed = child is not None
			if child_existed:
				dst = child
				if src.isdir():
					dst.must_be_dir()
				elif dst.isdir():
					raise IsADirectoryError(dst.path())
			else:
				dst = dst.add_child(src.fname,
							children=src.isdir(),
							volatile=True)
		else:
			child_existed = not dst.volatile

		# If @dst is not newly created by this invocation of the
		# function, @src must overwrite something.
		if child_existed and not dst.isdir():
			match self.file_exists(dst.path(), src.path()):
				case self.IfExists.FAIL:
					raise FileExistsError(dst.path())
				case self.IfExists.SKIP:
					movemap[src] = None
					return
				case self.IfExists.OVERWRITE:
					pass

		movemap[src] = dst
		if src.isdir():
			for child in src:
				self.map_moves(movemap, child, dst)

	# Actually move/copy/delete GCS blobs.
	def move_blob(self,
			src: VirtualGlobber.DirEnt,
			dst: VirtualGlobber.DirEnt) -> None:
		if self.encrypt_metadata:
			# @src's metadata has been updated to @dst's user path
			# by the caller.
			if not dst.volatile:
				# "Overwrite" @dst.  Make it certain
				# that we don't delete the wrong blob.
				assert dst.obj.blob_name != src.obj.blob_name
				dst.obj.gcs_blob.delete()
			return

		blob = src.obj
		old_gcs_blob = blob.gcs_blob
		new_blob_name = str(self.prefix / blob.user_path)
		generation = 0 if dst.volatile else None

		if self.is_hfs:
			# We're not creating a new GCS blob, but the
			# object referring to it will be new.
			blob.gcs_blob = self.bucket.move_blob(
						old_gcs_blob,
						new_blob_name,
						if_generation_match=generation)
		else:	# Try to execute copy+delete as a transaction.
			new_gcs_blob = self.bucket.copy_blob(
						old_gcs_blob,
						self.bucket,
						new_blob_name,
						if_generation_match=generation)

			try:
				old_gcs_blob.delete(if_generation_match=generation)
			except:
				new_gcs_blob.delete()
				raise
			else:
				blob.gcs_blob = new_gcs_blob

	# Walk through @src and move the files and directories underneath
	# around as described in the @movemap.
	def exec_moves(self, movemap: dict[VirtualGlobber.DirEnt,
						VirtualGlobber.DirEnt],
			uncommitted: list[tuple[VirtualGlobber.DirEnt,
						pathlib.PurePath]],
			src: DirEnt, move_blobs: bool = True) -> None:
		dst = movemap[src]
		if dst is None:
			# @dst exists and the user chose to skip it during
			# map_moves().
			print("Skipping %s." % src.path())
			return

		if not src.isdir():
			print("Moving %s to %s..." % (src.path(), dst.path()))

			blob = src.obj
			old_user_path = blob.user_path
			new_user_path = dst.path(full_path=True) \
						.relative_to(RootDir)

			# First update the metadata, which can be rolled back
			# by the top-level caller.
			uncommitted.append((src, old_user_path))
			blob.user_path = new_user_path
			blob.sync_metadata(update_mtime=False)

			if not move_blobs:
				# One of our callers will take care of it.
				return
			self.move_blob(src, dst)

			# We're out of the danger zone.
			uncommitted.pop()
			dst.commit(blob)
			src.parent.remove(src)
			return

		# src.isdir()
		assert not src.is_tld()
		move_folders = move_blobs \
				and not self.encrypt_metadata \
				and self.is_hfs \
				and dst.volatile

		if move_folders:
			# This is important because we'll clear the list
			# if we succeed.
			assert not uncommitted

			# The parent of the @dst folder must exist.
			if dst.parent.volatile:
				folder_id = self.remote.gcs_prefix(dst.parent)
				assert folder_id is not None
				self.create_folder(folder_id)
				dst.parent.commit()

		for child in src:
			self.exec_moves(movemap, uncommitted, child,
				move_blobs=move_blobs and not move_folders)

		if move_folders:
			print("Moving %s/ to %s/..."
				% (src.path(), dst.path()))
			self.rename_folder(
				self.remote.gcs_prefix(src),
				self.remote.gcs_prefix(dst))

			for dent, _ in uncommitted:
				movemap[dent].commit(dent.obj)
			uncommitted.clear()

			# Renaming the folder invalidated all GCS Blob objects
			# underneath because their names have changed.  It will
			# be cheaper to reload the subtree later than reloading
			# all the descendants individually.
			dst.unload_children()

		dst.commit()
		if self.remote.cwd is src:
			self.remote.cwd = dst

		if move_folders or (move_blobs and not src.children):
			if not move_folders:
				self.delete_folder(self.remote.gcs_prefix(src))
			src.parent.remove(src)

class CmdFTPCat(CmdExec):
	cmd = "cat"
	help = "TODO"

	head: Optional[int] = None
	what: list[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()

		self.sections["operation"].add_int_argument("--head", "-c")
		self.sections["positional"].add_argument("what", nargs='+')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.head = args.head
		self.what = args.what

	def files_to_cat(self) -> VirtualGlobber.DirEnt:
		# Prevent the Progressometer from messing up the output.
		with self.override_flags(progress=None):
			for match in self.remote.globs(self.what):
				src = self.remote.lookup(match)
				if src.isdir():
					raise IsADirectoryError(src.path())
				yield src

	def cat(self, src: VirtualGlobber.DirEnt,
			output: Optional[Pipeline.StdioType] = None) -> None:
		if self.head is None:
			# Send all of @src to @output.
			assert output is not None
			download_blob(self, src.obj, pipeline_stdout=output)
			return

		# Add cat(maxbytes=self.head) to the download Pipeline.
		cmd = { "executable": cat }
		cnt_r, cnt_w = Pipeline.Subprocess.add_pipe(cmd)
		cmd["args"] = { "maxbytes": self.head, "counter": cnt_w }

		# Since cat() won't read all the downloaded bytes,
		# a BrokenPipeError will be raised even on success.
		# Use the pipe created above to determine whether
		# this is the case.
		try:
			download_blob(self, src.obj, command=cmd,
					pipeline_stdout=output)
		except FatalError as ex:
			isok = False
			if isinstance(ex.__cause__, BrokenPipeError):
				try:	n = cnt_r.recv()
				except:	pass
				else:	# cat() finished successfully.
					assert n <= self.head
					isok = True
			if not isok:
				raise

	def execute(self) -> None:
		if self.head is None:
			# Just pass the file contents through,
			# it could be binary.
			output = os.fdopen(sys.stdout.fileno(), "wb",
						closefd=False)
		else:
			output = None

		for src in self.files_to_cat():
			self.cat(src, output)

class CmdFTPPage(CmdFTPCat):
	cmd = ("page", "less")
	help = "TODO"

	def execute(self) -> None:
		for src in self.files_to_cat():
			# If less(1) is the pager, show the file name
			# in the status line.
			env = os.environ.copy()
			lessopt = "-Ps" + str(src.path())
			if "LESS" in env:
				env["LESS"] += ' ' + lessopt
			else:
				env["LESS"] = lessopt

			pager = subprocess.Popen(
				("sensible-pager",), env=env,
				stdin=subprocess.PIPE)
			self.cat(src, pager.stdin)

			pager.stdin.close()
			pager.wait()

class CmdFTPGet(CmdExec, FTPOverwriteOptions):
	cmd = "get"
	help = "TODO"

	class Overwrite(Choices, enum.Enum):
		IN_PLACE	= enum.auto()	# Needs write permission.
		SEMI_ATOMIC	= enum.auto()	# Likewise.
		ATOMIC		= enum.auto()	# Needs read permission.

	keep_mtime: bool = True
	overwrite: Overwrite = Overwrite.SEMI_ATOMIC

	src: list[str]
	dst: Optional[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["operation"]
		section.add_disable_flag_no_dflt("--no-keep-mtime")

		choices = self.Overwrite.to_choices()
		section.add_argument("--overwrite", choices=choices)

		self.sections["positional"].add_argument("what", nargs='+')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.dst = args.what.pop() if len(args.what) > 1 else None
		self.src = args.what

	def post_validate(self, args: argparse.Namespace) -> None:
		super().post_validate(args)

		self.merge_options_from_ini(args, "keep_mtime", tpe=bool)
		if args.keep_mtime is not None:
			self.keep_mtime = args.keep_mtime

		choices = self.find_argument("--overwrite")[1]["choices"]
		self.merge_options_from_ini(args, "overwrite", tpe=choices)
		if args.overwrite is not None:
			self.overwrite = self.Overwrite.from_choice(
							args.overwrite)

	def execute(self) -> None:
		cmd_ftp_get(self)

	# Returns:
	# * file object
	# * None:	skip the file
	# * SystemExit:	abort the operation
	# * Exception:	fail the operation
	def open_dst(self, dst: pathlib.PurePath) -> Optional[BinaryIO]:
		if self.if_exists != self.IfExists.OVERWRITE:
			try:
				return open(dst, "xb")
			except FileExistsError:
				match self.file_exists(dst):
					case self.IfExists.FAIL:
						raise
					case self.IfExists.SKIP:
						return None

		if self.overwrite == self.Overwrite.IN_PLACE:
			return open(dst, "wb")

		# We need to open it for reading as well otherwise FICLONE
		# will fail with EBADF.
		import tempfile
		return tempfile.NamedTemporaryFile(
			dir=dst.parent, prefix=dst.name + '.',
			mode="x+b")

	# Copy all attributes of @dst to @tmp except the timestamps,
	# then replace @dst with @tmp.
	def atomic_overwrite(self, dst: pathlib.PurePath, tmp: BinaryIO) \
			-> None:
		subprocess.check_call((
			"cp", "--attributes-only",
			"--preserve=all",
			"--no-preserve=timestamps",
			str(dst), tmp.name,
		))
		os.rename(tmp.name, dst)

	# Clone the contents of @tmp into @dst, falling back to
	# atomic_overwrite() if ioctl(FICLONE) is not supported.
	def clone_file(self, dst: pathlib.PurePath, tmp: BinaryIO) -> BinaryIO:
		try:	# Open @dst without truncating it to be as atomic
			# as possible.
			fd = os.open(dst, os.O_WRONLY)
		except FileNotFoundError:
			# We were to overwrite @dst, but it doesn't exist
			# anymore.
			os.rename(tmp.name, dst)
			return tmp
		except PermissionError:
			self.atomic_overwrite(dst, tmp)
			return tmp

		# FICLONE fails if @fd is larger than @tmp.
		if os.stat(fd).st_size > tmp.tell():
			os.truncate(fd, tmp.tell())

		# Clone @tmp from the beginning to the end.
		tmp.seek(0)
		try:
			fcntl.ioctl(fd, FICLONE, tmp.fileno())
		except OSError as ex:
			os.close(fd)
			if ex.errno not in (
					errno.EOPNOTSUPP,
					errno.EINVAL, errno.EPERM):
				# An unexpected error.
				raise
			self.atomic_overwrite(dst, tmp)
			return tmp
		else:
			return os.fdopen(fd, "wb")

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
	except OSError as ex:
		raise FatalError from ex

	if local_isdir is False and (len(remote) > 1 or remote[0][1].isdir()):
		raise NotADirectoryError(local)
	elif local_isdir is None and len(remote) > 1:
		raise FileNotFoundError(local)

	nfiles = nbytes = duration = 0
	for src_path, src_top in remote:
		src_tree = src_top.scan()
		dst_top = local

		if local_isdir:
			if self.re_baseless.search(src_path):
				# Omit @src_top itself from the scan().
				src_tree = src_top.scan(pre_order=None)
			else:
				dst_top /= src_top.fname

		for src_dent in src_tree:
			dst_path = dst_top / src_dent.path(src_top)
			if src_dent.isdir():
				try:
					os.mkdir(dst_path)
				except FileExistsError:
					pass
				else:
					print(f"Created {dst_path}.")
				continue

			try:
				dst = self.open_dst(dst_path)
			except SystemExit:
				# Abort the operation.
				break
			except OSError as ex:
				raise FatalError from ex
			if dst is None:
				# Skip the file.
				continue

			try:
				src_path = src_dent.path()
				msg = f"Downloading {src_path}"

				# Similar logic as in upload_file().
				if not dst_path.is_absolute():
					src_path = src_path.relative_to(
								RootDir)
				if dst_path != src_path:
					msg += f" to {dst_path}"

				print(f"{msg}...", end="", flush=True)
				started = time.monotonic()
				nbytes += download_blob(self,
						src_dent.obj,
						pipeline_stdout=dst)
				duration += time.monotonic() - started
				nfiles += 1
			finally:
				print()

			dst.flush()
			if hasattr(dst, "file"):
				# @dst was created with tempfile.
				if self.overwrite == self.Overwrite.ATOMIC:
					self.atomic_overwrite(dst_path, dst)
				else:	# self.Overwrite.SEMI_ATOMIC
					dst = self.clone_file(dst_path, dst)

			if self.keep_mtime:
				# Set @dst's mtime to the blob's.
				os.utime(dst.fileno(), times=(
					time.time(),
					src_dent.obj.user_mtime.timestamp()))

			# Handle write errors before beginning the next cycle.
			try:
				dst.close()
			except FileNotFoundError:
				# Ignore the error if @dst is a tempfile,
				# it could have been renamed to @dst_path.
				if not hasattr(dst, "file"):
					raise
		else:	# Loop finished without interruption,
			# skip the "break" below.
			continue

		# open_dst() raised SystemExit in the inner loop to abort the
		# operation.
		break

	if nfiles > 1:
		print()
		print("Downloaded %d file(s) (%s) in %s."
			% (nfiles, humanize_size(nbytes),
				humanize_duration(duration)))

class CmdFTPPut(CmdExec, FTPOverwriteOptions):
	cmd = "put"
	help = "TODO"

	follow_symlinks: bool

	cmd: Optional[str]
	src: list[str]
	dst: Optional[str]

	def declare_arguments(self) -> None:
		super().declare_arguments()

		section = self.sections["operation"]
		mutex = section.add_mutually_exclusive_group()
		mutex.add_enable_flag("--follow-symlinks", "--dereference",
					"-L")
		mutex.add_enable_flag("--stdin", "-s")
		mutex.add_argument("--cmd", "-c")

		self.sections["positional"].add_argument("what", nargs='+')

	def pre_validate(self, args: argparse.Namespace) -> None:
		super().pre_validate(args)

		self.follow_symlinks = args.follow_symlinks

		if args.stdin or args.cmd is not None:
			if len(args.what) > 1:
				raise self.CmdLineError(
					"a single destination "
					"must be specified")
			self.dst = args.what[0]
			self.src = [ ]

			if args.cmd is not None:
				self.cmd = args.cmd
			elif self.if_exists == self.IfExists.ASK:
				# Once we've read stdin we can't read it again.
				raise self.CmdLineError(
					"can't use --stdin with --exists ask")
			else:
				self.cmd = None
		else:
			self.cmd = None
			self.dst = args.what.pop() \
					if len(args.what) > 1 \
					else None
			self.src = args.what

	def execute(self) -> None:
		cmd_ftp_put(self)

# Wrapper around @callback, which should upload_blob().
# Returns the number of bytes uploaded and the time it took.
def try_to_upload(self: _CmdFTPPut|_CmdFTPTouch,
			blob: MetaBlob, dst: VirtualGlobber.DirEnt,
			callback: Callable[[Any], int],
			msg: Optional[str] = None) \
			-> tuple[Optional[int], Optional[float]]:
	if msg is not None:
		print(f"{msg}...", end="", flush=True)
		sep = ' '
	else:
		sep = ""

	overwrite = (self.if_exists == self.IfExists.OVERWRITE)
	if not dst.volatile and not overwrite:
		match self.file_exists(dst.path(), prompt=f"{sep}blob exists"):
			case self.IfExists.FAIL:
				if msg is not None:
					print()
				raise FileExistsError(dst.path())
			case self.IfExists.SKIP:
				return None, None
			case self.IfExists.OVERWRITE:
				overwrite = True
				if msg is not None:
					print(f"{msg}...", end="", flush=True)

	try:
		started = time.monotonic()
		nbytes = callback(
				blob=blob, padding=self.padding,
				overwrite=None if overwrite else False)
	except Exception:
		print()
		raise

	duration = time.monotonic() - started
	print()

	dst.commit(blob)
	return nbytes, duration

def upload_file(self: _CmdFTPPut|_CmdFTPTouch,
		src_path: Union[str, pathlib.PurePath],
		dst_path: pathlib.PurePath,
		dst_dent: Optional[VirtualGlobber.DirEnt] = None,
		msg: Optional[str] = None) \
		-> tuple[Optional[int], Optional[float]]:
	if msg is None:
		msg = f"Uploading {src_path}"
		if not isinstance(src_path, pathlib.PurePath):
			src_path = pathlib.PurePath(src_path)

		# @dst_path is absolute, @src_path can be either
		# ("ftp put this" or "ftp put /that").
		if src_path.is_absolute():
			same = (dst_path == src_path)
		else:
			same = (dst_path.relative_to(RootDir) == src_path)
		if not same:
			msg += f" as {dst_path}"

	if dst_dent is None:
		dst_dent = self.remote.lookup(dst_path, create=True)
	assert not dst_dent.isdir()

	if dst_dent.volatile:
		# Make @full_dst non-absolute, looks nicer in the GCS console.
		full_dst = self.remote.root.path(full_path=True)
		full_dst /= dst_path.relative_to(RootDir)
		blob = MetaBlob(self, full_dst.relative_to(RootDir))
	else:
		blob = dst_dent.obj
		assert blob is not None

	# Reopen @src_path every time we try, in order to read from the
	# beginning (it might not be seekable).
	fun = lambda **kw: \
		upload_blob(self, pipeline_stdin=open(src_path, "rb"), **kw)
	return try_to_upload(self, blob, dst_dent, fun, msg)

def cmd_ftp_put(self: _CmdFTPPut) -> None:
	# @local := list of source paths as strings
	if isinstance(self.parent, CmdFTPShell):
		try:
			local = list(self.local.globs(
					map(os.path.expanduser, self.src)))
		except OSError as ex:
			raise FatalError from ex
	else:
		local = self.src

	# @local := [ (local path string, st_mode), ... ]
	# Also verify that all the paths are reachable and is either a regular
	# file or directory.
	for i, src in enumerate(local):
		try:
			mode = os.stat(src).st_mode
		except OSError as ex:
			raise FatalError from ex
		if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
			raise UserError(
				f"{src}: not a regular file or directory")
		local[i] = (src, mode)

	# @remote := the destination DirEnt (possibly created provisionally)
	if self.dst is not None:
		remote = self.remote.lookup(
				self.remote.glob(self.dst,
						at_least_one=True,
						at_most_one=True,
						must_exist=False),
				create=True)
	else:
		remote = self.remote.cwd

	# Handle --stdin and --cmd.
	if not self.src:
		if remote.isdir():
			raise IsADirectoryError(remote.path())

		if not remote.volatile:
			# Replace the existing blob if we're overwriting.
			assert remote.obj is not None
			blob = remote.obj
		else:
			blob = MetaBlob(self,
				remote.path(full_path=True).relative_to(RootDir))

		if self.cmd is None:
			msg = "Uploading from stdin"
			def fun(**kw):
				# Add a newline to @msg if stdin is a TTY.
				if self.interactive:
					print(f"{msg} (^D to finish)...")
				return upload_blob(self,
						pipeline_stdin=os.fdopen(
							sys.stdin.fileno(),
							closefd=False),
						**kw)

			try_to_upload(self, blob, remote, fun,
				None if self.interactive else msg)
		else:
			fun = lambda **kw: \
				upload_blob(self, command=self.cmd, **kw)
			try_to_upload(self, blob, remote, fun,
				"Uploading from %s" % shlex.quote(self.cmd))
		return

	# If @remote is not a directory, @local must be a single regular file.
	if (len(local) > 1 or stat.S_ISDIR(local[0][1])) \
			and not remote.isdir():
		if remote.volatile:
			raise FileNotFoundError(remote.path())
		else:
			raise NotADirectoryError(remote.path())

	# The set of directories we've processed.  Used to protect against
	# symlink loops.
	seen = set() if self.follow_symlinks else None

	# The os.walk(onerror) handler.
	def walk_error(ex: Exception) -> None:
		raise FatalError from ex

	aborted = False
	nfiles = nbytes = duration = 0
	remote_was_volatile = remote.volatile
	for src_path, src_mode in local:
		if stat.S_ISREG(src_mode):
			dst_path = remote.path()
			if remote.isdir():
				dst_path /= os.path.basename(src_path)
			try:
				n, t = upload_file(self, src_path, dst_path)
			except OSError as ex:
				raise FatalError from ex
			except SystemExit:
				break
			if n is not None:
				nbytes += n
				nfiles += 1
				duration += t
			continue

		# @src_path is a directory.
		src_top = pathlib.PurePath(src_path)
		dst_top = remote.path()
		if not remote_was_volatile \
				and not self.re_baseless.search(src_path):
			# put foo bar -> upload foo/* under bar/foo/*
			# Otherwise upload foo/* under bar/*.
			dst_top /= src_top.name

		# Walk the tree of @src_top.
		for src_dir, dirs, files in os.walk(
				src_top, followlinks=self.follow_symlinks,
				onerror=walk_error):
			# @dst_dir := @src_dir [@src_top -> @dst_top]
			src_dir = pathlib.PurePath(src_dir)
			dst_dir = dst_top / src_dir.relative_to(src_top)

			# Upload the @files in a predictable order.
			for fname in sorted(files):
				src_path = src_dir / fname
				dst_path = dst_dir / fname

				try:
					src_mode = os.stat(src_path).st_mode
				except OSError as ex:
					# Skip dangling and self-referencing
					# symlinks, and also files gone during
					# the scan.
					if ex.errno in (errno.ENOENT,
							errno.ELOOP):
						print(f"{ex.filename}: "
							f"{ex.strerror}",
							file=sys.stderr)
						continue
					raise FatalError from ex

				if not stat.S_ISREG(src_mode):
					# Skip pipes, devices etc.
					print("%s: not a regular file"
							% src_path,
						file=sys.stderr)
					continue

				try:
					n, t = upload_file(self,
							src_path, dst_path)
				except OSError as ex:
					raise FatalError from ex
				except SystemExit:
					aborted = True
					break
				if n is not None:
					nbytes += n
					nfiles += 1
					duration += t

			if aborted:
				break

			if seen is not None:
				# Remove directories from @dirs we've @seen.
				sbuf = os.stat(src_dir)
				seen.add((sbuf.st_dev, sbuf.st_ino))

				i = 0
				remove = [ ]
				for dname in dirs:
					sbuf = os.stat(src_dir / dname)
					if (sbuf.st_dev, sbuf.st_ino) in seen:
						remove.append(i)
					else:
						i += 1

				for i in remove:
					del dirs[i]

			# Traverse @dirs in a predictable order.
			dirs.sort()

		if aborted:
			break

	if nfiles > 1:
		print()
		print("Uploaded %d file(s) (%s) in %s."
			% (nfiles, humanize_size(nbytes),
				humanize_duration(duration)))

class CmdFTPTouch(FTPOverwriteOptions, CmdExec):
	cmd = "touch"
	help = "TODO"

	what: list[str]

	def declare_arguments(self) -> None:
		# We need FTPOverwriteOptions for try_to_upload(),
		# but we don't want to declare any flags.
		super(FTPOverwriteOptions, self).declare_arguments()
		self.sections["positional"].add_argument("what", nargs='+')

	def pre_validate(self, args: argparse.Namespace) -> None:
		# Like above.
		super(FTPOverwriteOptions, self).pre_validate(args)
		self.what = args.what

	def execute(self: _CmdFTPTouch) -> None:
		for path in self.remote.globs(self.what, must_exist=False):
			dent = self.remote.lookup(path, create=True)
			path = dent.path()

			if dent.isdir():
				if dent.volatile:
					# User should use mkdir instead.
					raise IsADirectoryError(path)
			elif dent.volatile:
				upload_file(self, "/dev/null", path, dent,
						f"Creating {path}...")
			else:	# This will update the mtime.
				print(f"Touching {path}...")
				dent.obj.sync_metadata()

class _CmdFTPChDir(CmdFTP, CmdFTPChDir): pass
class _CmdFTPPwd(CmdFTP, CmdFTPPwd): pass
class _CmdFTPPushD(CmdFTP, CmdFTPPushD): pass
class _CmdFTPPopD(CmdFTP, CmdFTPPopD): pass
class _CmdFTPDirStack(CmdFTP, CmdFTPDirStack): pass
class _CmdFTPTree(CmdFTP, CmdFTPTree): pass
class _CmdFTPDir(CmdFTP, CmdFTPDir): pass
class _CmdFTPPDir(CmdFTP, CmdFTPPDir): pass
class _CmdFTPDu(CmdFTP, CmdFTPDu): pass
class _CmdFTPMkDir(CmdFTP, CmdFTPMkDir): pass
class _CmdFTPRmDir(CmdFTP, CmdFTPRmDir): pass
class _CmdFTPRm(CmdFTP, CmdFTPRm): pass
class _CmdFTPMove(CmdFTP, CmdFTPMove): pass
class _CmdFTPGet(CmdFTP, CmdFTPGet): pass
class _CmdFTPPut(CmdFTP, CmdFTPPut): pass
class _CmdFTPTouch(CmdFTP, CmdFTPTouch): pass

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
