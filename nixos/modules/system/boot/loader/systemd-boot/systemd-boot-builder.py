#! @python3@/bin/python3 -B
import argparse
import ctypes
import datetime
import errno
import functools
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import warnings
import json
import stat
import struct
from typing import NamedTuple, Any, Protocol, Sequence, BinaryIO
from dataclasses import dataclass, field
from pathlib import Path

# These values will be replaced with actual values during the package build
EFI_SYS_MOUNT_POINT = Path("@efiSysMountPoint@")
BOOT_MOUNT_POINT = Path("@bootMountPoint@")
LOADER_CONF = EFI_SYS_MOUNT_POINT / "loader/loader.conf"  # Always stored on the ESP
NIXOS_DIR = Path(
    "@nixosDir@".strip("/")
)  # Path relative to the XBOOTLDR or ESP mount point
TIMEOUT = "@timeout@"
EDITOR = "@editor@" == "1"  # noqa: PLR0133
CONSOLE_MODE = "@consoleMode@"
DISTRO_NAME = "@distroName@"
NIX = "@nix@"
SYSTEMD = "@systemd@"
CONFIGURATION_LIMIT = int("@configurationLimit@")
REBOOT_FOR_BITLOCKER = bool("@rebootForBitlocker@")
CAN_TOUCH_EFI_VARIABLES = "@canTouchEfiVariables@" == "1"
GRACEFUL = "@graceful@" == "1"
COPY_EXTRA_FILES = "@copyExtraFiles@"
CHECK_MOUNTPOINTS = "@checkMountpoints@"
PREPARE_EXTRA_FILES = "@prepareExtraFiles@"
STORE_DIR = "@storeDir@"
BOOT_COUNTING_TRIES = "@bootCountingTries@"
BOOT_COUNTING = "@bootCounting@" == "True"
UKI_CONFIG = json.loads(Path("@ukiConfig@").read_text())


@dataclass(frozen=True)
class BootSpec:
    init: Path
    initrd: Path
    extraInitrdPaths: list[Path]
    kernel: Path
    kernelParams: list[str]  # noqa: N815
    label: str
    system: str
    toplevel: Path
    specialisations: dict[str, "BootSpec"]
    sortKey: str  # noqa: N815
    devicetree: Path | None = None  # noqa: N815
    initrdSecrets: str | None = None  # noqa: N815
    uname: str | None = None
    extraInitrdSources: dict[str, str] = field(default_factory=dict)  # noqa: N815


class WriteBootFile(Protocol):
    def write_boot_file(self, path: Path, *, critical: bool) -> None: ...


@dataclass
class CopyWriter:
    source: Path
    replace: bool = False

    def write_boot_file(self, path: Path, *, critical: bool) -> None:
        if path.exists() and not self.replace:
            return
        copy_atomically(self.source, path)


def copy_atomically(source: Path, path: Path) -> None:
    with tempfile.NamedTemporaryFile(
        mode="wb",
        dir=path.parent,
        delete=False,
        prefix=path.name,
        suffix=".tmp",
    ) as tmp:
        try:
            with open(source, mode="rb") as source_file:
                shutil.copyfileobj(source_file, tmp)
            tmp.flush()
            os.fsync(tmp.fileno())
        except BaseException:
            os.unlink(tmp.name)
            raise
    os.rename(tmp.name, path)


@dataclass
class InitrdWithSecretsWriter:
    source: Path
    initrd_secrets: Path
    generation: int

    def write_boot_file(self, path: Path, *, critical: bool) -> None:
        # Secrets can change between rebuilds, so always rebuild from the
        # pristine initrd into a temp file and rename into place.
        with tempfile.NamedTemporaryFile(
            mode="wb",
            dir=path.parent,
            delete=False,
            prefix=path.name,
            suffix=".tmp",
        ) as tmp:
            try:
                with open(self.source, mode="rb") as source_file:
                    shutil.copyfileobj(source_file, tmp)
                tmp.flush()
                run([self.initrd_secrets, tmp.name])
                os.fsync(tmp.fileno())
            except subprocess.CalledProcessError:
                os.unlink(tmp.name)
                if critical:
                    print("failed to create initrd secrets!", file=sys.stderr)
                    sys.exit(1)
                # Keep the entry bootable by leaving at least a pristine
                # initrd in place. CopyWriter is a no-op if one already
                # exists.
                retained = path.exists()
                CopyWriter(source=self.source).write_boot_file(path, critical=False)
                print(
                    "warning: failed to update initrd secrets for an older "
                    f"generation ({self.generation}). "
                    + (
                        "The previous installed initrd is retained. "
                        if retained
                        else "Using the pristine initrd without runtime secrets. "
                    )
                    + "To silence "
                    "this warning, restore the secret files to their "
                    "original locations or delete this generation.",
                    file=sys.stderr,
                )
                return
            except BaseException:
                os.unlink(tmp.name)
                raise
            os.rename(tmp.name, path)


@dataclass
class ContentsWriter:
    contents: bytes

    def write_boot_file(self, path: Path, *, critical: bool) -> None:
        if path.exists():
            return
        with tempfile.NamedTemporaryFile(
            mode="wb",
            dir=path.parent,
            delete=False,
            prefix=path.name,
            suffix=".tmp",
        ) as tmp:
            tmp.write(self.contents)
            tmp.flush()
            os.fsync(tmp.fileno())
            tmp.close()
            os.rename(tmp.name, path)


class SystemIdentifier(NamedTuple):
    profile: str | None
    generation: int
    specialisation: str | None


@dataclass
class BootFile:
    path: Path
    writer: WriteBootFile

    @staticmethod
    def from_source(source: Path) -> "BootFile":
        return BootFile(
            path=boot_path(source),
            writer=CopyWriter(source=source),
        )

    @staticmethod
    def from_initrd(
        generation: int,
        source: Path,
        initrd_secrets: Path | None,
    ) -> "BootFile":
        if initrd_secrets is None:
            return BootFile.from_source(source)
        else:
            # We're trying to calculate a canonical path unique to
            # this initrd and secret-appender. The boot_path is the
            # canonical path for files that don't need modifications,
            # so it serves as a perfect proxy for the unique
            # information to combine for a combined unique path. The
            # original paths themselves would have also been fine, but
            # boot_path is more semantically representative, since
            # it's the actual path whose uniqueness we're trying to
            # ensure for other things.
            combined = "\n".join(
                [str(boot_path(source)), str(boot_path(initrd_secrets))]
            )
            combined_hash = hashlib.sha256(combined.encode("utf-8")).hexdigest()
            return BootFile(
                path=NIXOS_DIR / f"{combined_hash}-initrd.efi",
                writer=InitrdWithSecretsWriter(
                    source=source,
                    initrd_secrets=initrd_secrets,
                    generation=generation,
                ),
            )

    @staticmethod
    def from_entry(contents: bytes) -> tuple["BootFile", str]:
        contents_hash = hashlib.sha256(contents).hexdigest()
        path_prefix = f"nixos-{contents_hash}"
        pat = re.compile(rf"{re.escape(path_prefix)}(\+[0-9]+(-[0-9]+)?)?\.conf")
        path = None
        for e in os.scandir(path=BOOT_MOUNT_POINT / "loader" / "entries"):
            if pat.fullmatch(e.name) is None:
                continue
            # Ignore files whose content does not match the hash in their
            # name so GC removes them and a fresh entry is written.
            if hashlib.sha256(Path(e.path).read_bytes()).hexdigest() != contents_hash:
                continue
            path = Path("loader/entries") / e.name
            break
        if path is None:
            counters = f"+{BOOT_COUNTING_TRIES}" if BOOT_COUNTING else ""
            path = Path(f"loader/entries/{path_prefix}{counters}.conf")
        return (
            BootFile(
                path=path,
                writer=ContentsWriter(contents=contents),
            ),
            f"{path_prefix}.conf",
        )


# This gets its own type alias to document that the order is very
# important. The order ensures that entry files are written after
# their respective kernel / initrd / etc.
type BootFileList = list[BootFile]


libc = ctypes.CDLL("libc.so.6", use_errno=True)

FILE = None | int


def run(
    cmd: Sequence[str | Path], stdout: FILE = None
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, check=True, text=True, stdout=stdout, stderr=sys.stderr)


def bootctl_varlink_call(method: str, parameters: dict[str, Any]) -> dict[str, Any]:
    # Spawn bootctl as a Varlink server on stdio, mirroring what varlinkctl
    # does when given an executable path. We cannot talk to a running
    # systemd-bootctl.socket because that would use bootctl from the booted
    # system rather than the closure we are switching to, does not let us set
    # SYSTEMD_ESP_PATH/SYSTEMD_XBOOTLDR_PATH, and is unavailable inside
    # nixos-enter anyway.
    env = os.environ | {
        "SYSTEMD_VARLINK_LISTEN": "-",
        "SYSTEMD_ESP_PATH": str(EFI_SYS_MOUNT_POINT),
    }
    if BOOT_MOUNT_POINT != EFI_SYS_MOUNT_POINT:
        env["SYSTEMD_XBOOTLDR_PATH"] = str(BOOT_MOUNT_POINT)

    proc = subprocess.Popen(
        [f"{SYSTEMD}/bin/bootctl"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=sys.stderr,
        env=env,
    )
    assert proc.stdin is not None and proc.stdout is not None
    request = json.dumps({"method": method, "parameters": parameters}).encode()
    out, _ = proc.communicate(request + b"\0")
    reply, _, _ = out.partition(b"\0")
    if not reply:
        raise RuntimeError(
            f"bootctl exited with status {proc.returncode} without a Varlink reply"
        )
    return json.loads(reply)


def generation_dir(profile: str | None, generation: int) -> Path:
    if profile:
        return Path(
            f"/nix/var/nix/profiles/system-profiles/{profile}-{generation}-link"
        )
    else:
        return Path(f"/nix/var/nix/profiles/system-{generation}-link")


def system_dir(
    profile: str | None, generation: int, specialisation: str | None
) -> Path:
    d = generation_dir(profile, generation)
    if specialisation:
        return d / "specialisation" / specialisation
    else:
        return d


def write_loader_conf(default_entry_id: str | None) -> None:
    tmp = LOADER_CONF.with_suffix(".tmp")
    with tmp.open("x") as f:
        f.write(f"timeout {TIMEOUT}\n")
        if default_entry_id is None:
            # No generation matched the requested default config; fall back to
            # the newest entry as determined by Boot Loader Spec sorting.
            f.write("default nixos-*\n")
        elif BOOT_COUNTING:
            # `preferred` (systemd-boot >= 260) honours boot assessment, so a
            # generation that exhausted its boot counter is skipped and we fall
            # through to `default`. systemd-boot sorts entries with
            # tries_left == 0 to the end of the list and resolves the `default`
            # glob against that order, so `nixos-*` yields the newest entry that
            # is not bad, or a bad one only if every nixos entry is bad.
            f.write(f"preferred {default_entry_id}\n")
            f.write("default nixos-*\n")
        else:
            f.write(f"default {default_entry_id}\n")
        if not EDITOR:
            f.write("editor 0\n")
        if REBOOT_FOR_BITLOCKER:
            f.write("reboot-for-bitlocker yes\n")
        f.write(f"console-mode {CONSOLE_MODE}\n")
        f.flush()
        os.fsync(f.fileno())
    os.rename(tmp, LOADER_CONF)


def get_bootspec(profile: str | None, generation: int) -> BootSpec | None:
    system_directory = system_dir(profile, generation, None)
    boot_json_path = (system_directory / "boot.json").resolve()
    if not boot_json_path.is_file():
        print(
            f"warning: skipping generation {generation}"
            + (f" of profile {profile}" if profile else "")
            + f": {boot_json_path} does not exist",
            file=sys.stderr,
        )
        return None
    with boot_json_path.open("r") as f:
        # check if json is well-formed, else throw error with filepath
        try:
            bootspec_json = json.load(f)
        except ValueError as e:
            print(f"error: Malformed Json: {e}, in {boot_json_path}", file=sys.stderr)
            sys.exit(1)
    return bootspec_from_json(bootspec_json)


def bootspec_from_json(bootspec_json: dict[str, Any]) -> BootSpec:
    specialisations = bootspec_json["org.nixos.specialisation.v1"]
    specialisations = {k: bootspec_from_json(v) for k, v in specialisations.items()}
    systemdBootExtension = bootspec_json.get("org.nixos.systemd-boot", {})
    sortKey = systemdBootExtension.get("sortKey", "nixos")
    devicetree = systemdBootExtension.get("devicetree")

    extraInitrdExtension = bootspec_json.get("org.nixos.extra-initrd.v1", {})
    extraInitrdPaths = list(
        map(lambda path: Path(path), extraInitrdExtension.get("paths", []))
    )

    if devicetree:
        devicetree = Path(devicetree)

    main_json = bootspec_json["org.nixos.bootspec.v1"]
    for attr in ("kernel", "initrd", "toplevel"):
        if attr in main_json:
            main_json[attr] = Path(main_json[attr])
    return BootSpec(
        **main_json,
        specialisations=specialisations,
        sortKey=sortKey,
        devicetree=devicetree,
        extraInitrdPaths=extraInitrdPaths,
        uname=systemdBootExtension.get("uname"),
        extraInitrdSources={
            str(Path(path)): source
            for path, source in systemdBootExtension.get(
                "extraInitrdSources", {}
            ).items()
        },
    )


@functools.lru_cache(maxsize=None)
def boot_path(file: Path) -> Path:
    store_file_path = file.resolve()
    suffix = store_file_path.name
    store_subdir = store_file_path.relative_to(STORE_DIR).parts[0]
    return NIXOS_DIR / (
        f"{suffix}.efi" if suffix == store_subdir else f"{store_subdir}-{suffix}.efi"
    )


class PESection(NamedTuple):
    size: int
    raw_size: int
    offset: int


@dataclass
class PEHeader:
    machine: int
    entrypoint: int
    optional: int
    security: int
    certificate_offset: int
    sections: dict[str, PESection]

    @staticmethod
    def read(file: BinaryIO, length: int, path: Path) -> "PEHeader":
        def read_at(offset: int, size: int) -> bytes:
            if offset < 0 or offset + size > length:
                raise ValueError(f"Truncated PE image: {path}")
            file.seek(offset)
            data = file.read(size)
            if len(data) != size:
                raise ValueError(f"Truncated PE image: {path}")
            return data

        dos = read_at(0, 64)
        if dos[:2] != b"MZ":
            raise ValueError(f"Not a PE image: {path}")
        offset = struct.unpack_from("<I", dos, 60)[0]
        coff = read_at(offset, 24)
        if offset < 64 or coff[:4] != b"PE\0\0":
            raise ValueError(f"Invalid PE header: {path}")
        machine, count = struct.unpack_from("<HH", coff, 4)
        optional_size = struct.unpack_from("<H", coff, 20)[0]
        optional = offset + 24
        header = read_at(optional, optional_size)
        magic = struct.unpack_from("<H", header)[0] if optional_size >= 2 else 0
        directory_start = {0x10B: 96, 0x20B: 112}.get(magic)
        if directory_start is None or optional_size < directory_start + 5 * 8:
            raise ValueError(f"Missing PE security directory: {path}")
        directory_count = struct.unpack_from("<I", header, directory_start - 4)[0]
        if (
            directory_count < 5
            or directory_count > (optional_size - directory_start) // 8
        ):
            raise ValueError(f"Invalid PE data directories: {path}")
        security = optional + directory_start + 4 * 8
        certificate_offset, certificate_size = struct.unpack_from(
            "<II", header, directory_start + 4 * 8
        )
        table = read_at(optional + optional_size, count * 40)
        headers_end = optional + optional_size + len(table)
        sections: dict[str, PESection] = {}
        for index in range(count):
            position = index * 40
            try:
                name = table[position : position + 8].rstrip(b"\0").decode("ascii")
            except UnicodeDecodeError as error:
                raise ValueError(f"Invalid PE section name: {path}") from error
            size, _, raw_size, raw_offset = struct.unpack_from(
                "<IIII", table, position + 8
            )
            if name in sections or (
                raw_size
                and (raw_offset < headers_end or raw_offset + raw_size > length)
            ):
                raise ValueError(f"Invalid PE section: {path}: {name}")
            sections[name] = PESection(size, raw_size, raw_offset)
        if certificate_size:
            payload_end = max(
                [headers_end]
                + [
                    section.offset + section.raw_size
                    for section in sections.values()
                    if section.raw_size
                ]
            )
            if (
                certificate_offset < payload_end
                or certificate_offset + certificate_size != length
            ):
                raise ValueError(f"Invalid PE certificate table: {path}")
        elif certificate_offset:
            raise ValueError(f"Invalid empty PE certificate table: {path}")
        return PEHeader(
            machine,
            struct.unpack_from("<I", header, 16)[0],
            optional,
            security,
            certificate_offset,
            sections,
        )


@dataclass
class PEImage:
    data: bytes
    header: PEHeader

    @staticmethod
    def read(path: Path) -> "PEImage":
        # Parse headers using bounded reads; load executable bytes only once.
        with path.open("rb") as file:
            header = PEHeader.read(file, os.fstat(file.fileno()).st_size, path)
            file.seek(0)
            return PEImage(file.read(), header)

    def sections(self) -> dict[str, memoryview]:
        data = memoryview(self.data)
        return {
            # PE sections can have a zero-filled virtual tail. Keep the file
            # view bounded; compare virtual sizes separately for UKI payloads.
            name: data[
                section.offset : section.offset + min(section.size, section.raw_size)
            ]
            if section.raw_size
            else data[:0]
            for name, section in self.header.sections.items()
        }

    def digest(self, certificate: bytes = b"") -> str:
        # Authenticode changes the checksum, security directory, terminal
        # certificate table and alignment padding. Hash every other byte without
        # allocating a second full image or copies of its kernel/initrd sections.
        end = self.header.certificate_offset or len(self.data)
        while end and self.data[end - 1] == 0:
            end -= 1
        data = memoryview(self.data)
        identity = hashlib.sha256()
        position = 0
        for offset, size in ((self.header.optional + 64, 4), (self.header.security, 8)):
            identity.update(data[position : min(offset, end)])
            identity.update(b"\0" * max(0, min(size, end - offset)))
            position = offset + size
        identity.update(data[position:end])
        identity.update(certificate)
        return identity.hexdigest()


def sbverify_command(path: Path) -> list[str | Path]:
    return [UKI_CONFIG["sbverify"], "--cert", UKI_CONFIG["certificate"], path]


def verify_signature(path: Path) -> None:
    if UKI_CONFIG["certificate"] is not None:
        run(sbverify_command(path))


def check_signing_inputs() -> None:
    if UKI_CONFIG["privateKey"] is None:
        return
    key = Path(UKI_CONFIG["privateKey"])
    if not key.is_absolute() or key.resolve().is_relative_to(STORE_DIR):
        raise ValueError(
            "UKI private key must be an absolute path outside the Nix store"
        )
    info = key.stat()
    if not stat.S_ISREG(info.st_mode) or info.st_uid != 0 or info.st_mode & 0o077:
        raise ValueError(
            "UKI private key must be a private root-owned file outside the Nix store"
        )
    key = key.resolve()
    for parent in key.parents:
        info = parent.stat()
        if info.st_uid != 0 or info.st_mode & 0o022:
            raise ValueError(
                "UKI private key directories must be owned and writable only by root"
            )
    UKI_CONFIG["privateKey"] = str(key)
    # The certificate is public and may live in the immutable Nix store. Its
    # runtime path must still be protected against replacement by other users.
    certificate = Path(UKI_CONFIG["certificate"])
    if not certificate.is_absolute() or not certificate.is_file():
        raise ValueError(
            f"UKI certificate must be an absolute path to a PEM file: {certificate}"
        )
    certificate = certificate.resolve()
    protected_paths = (
        [certificate]
        if certificate.is_relative_to(STORE_DIR)
        else [certificate, *certificate.parents]
    )
    for protected in protected_paths:
        info = protected.stat()
        if info.st_uid != 0 or info.st_mode & 0o022:
            raise ValueError(
                f"UKI certificate and directories must be owned and writable only by root: {protected}"
            )

    UKI_CONFIG["certificate"] = str(certificate)


def manager_version(data: bytes) -> str | None:
    # Read the marker from raw bytes, as bootctl does, so a damaged or
    # unusually signed systemd-boot is still recognized and replaced.
    match = re.search(rb"#### LoaderInfo: systemd-boot (\S+) ####", data)
    return match.group(1).decode(errors="surrogateescape") if match else None


def is_signed(path: Path) -> bool:
    # Quiet probe: unsigned managers are expected before the first signed install.
    return subprocess.run(sbverify_command(path), capture_output=True).returncode == 0


def is_current_manager(path: Path, expected: str) -> bool:
    try:
        return PEImage.read(path).digest() == expected
    except ValueError:
        return False


def is_newer_version(version: str, than: str) -> bool:
    # Use systemd's own version ordering, as bootctl update does.
    command = [
        UKI_CONFIG["systemdAnalyze"],
        "compare-versions",
        version,
        "gt",
        than,
    ]
    return subprocess.run(command).returncode == 0


def stage_signed_managers(work: Path) -> list[tuple[Path, Path]]:
    # Keep a manager signed with the UKI key that is this build or newer, and
    # leave a foreign fallback loader alone. Replace anything else, even a newer
    # manager without this signature, with this build signed by the UKI key.
    arch = UKI_CONFIG["efiArch"]
    source = Path(SYSTEMD) / f"lib/systemd/boot/efi/systemd-boot{arch}.efi"
    expected = PEImage.read(source).digest()
    version = manager_version(source.read_bytes())
    if version is None:
        raise ValueError(f"Not a systemd-boot image: {source}")
    signed = work / source.name
    updates = []
    for relative, fallback in (
        (f"EFI/systemd/systemd-boot{arch}.efi", False),
        (f"EFI/BOOT/BOOT{arch.upper()}.EFI", True),
    ):
        installed = EFI_SYS_MOUNT_POINT / relative
        installed_version = (
            manager_version(installed.read_bytes()) if installed.exists() else None
        )
        if installed_version is None:
            if fallback and installed.exists():
                continue
        elif is_signed(installed) and (
            is_current_manager(installed, expected)
            or is_newer_version(installed_version, version)
        ):
            continue
        if not signed.exists():
            run(
                [
                    UKI_CONFIG["sbsign"],
                    "--key",
                    UKI_CONFIG["privateKey"],
                    "--cert",
                    UKI_CONFIG["certificate"],
                    "--output",
                    signed,
                    source,
                ]
            )
            verify_signature(signed)
            if PEImage.read(signed).digest() != expected:
                raise ValueError(f"Signed manager does not match {source}")
        updates.append((signed, installed))
    return updates


def install_signed_managers(updates: list[tuple[Path, Path]]) -> None:
    for signed, installed in updates:
        installed.parent.mkdir(parents=True, exist_ok=True)
        copy_atomically(signed, installed)
        print(f'Installed signed "{signed.name}" to "{installed}".', file=sys.stderr)


def uki_identifier(image: PEImage) -> str:
    certificate = (
        Path(UKI_CONFIG["certificate"]).read_bytes()
        if UKI_CONFIG["certificate"] is not None
        else b""
    )
    return image.digest(certificate)


# Payload sections ukify can add but this builder never does.
FOREIGN_UKI_SECTIONS = (
    ".ucode",
    ".splash",
    ".pcrsig",
    ".pcrpkey",
    ".profile",
    ".dtbauto",
    ".hwids",
    ".efifw",
)


def payload_mismatch(
    payload: PEImage, expected: dict[str, bytes], *, skip: str | None = None
) -> str | None:
    sections = payload.sections()
    for name, contents in expected.items():
        if name != skip and (
            sections.get(name) != contents
            or payload.header.sections[name].size != len(contents)
        ):
            return name
    for name in (".dtb", *FOREIGN_UKI_SECTIONS):
        if name not in expected and name in payload.header.sections:
            return name
    return None


@functools.cache
def retained_uki_candidates(work: Path) -> dict[bytes, list[Path]]:
    # Index the section table and command line once per installation. Large
    # payloads are read only for a matching closure, never cached across images.
    candidates: dict[bytes, list[Path]] = {}
    for image in sorted((BOOT_MOUNT_POINT / NIXOS_DIR).glob("*-uki.efi")):
        if re.fullmatch(r"[0-9a-f]{64}-uki\.efi", image.name) is None:
            continue
        try:
            with image.open("rb") as file:
                header = PEHeader.read(file, os.fstat(file.fileno()).st_size, image)
                section = header.sections.get(".cmdline")
                if section is None or not section.raw_size:
                    continue
                file.seek(section.offset)
                candidates.setdefault(
                    file.read(min(section.size, section.raw_size)), []
                ).append(image)
        except (OSError, ValueError) as error:
            print(
                f"warning: ignoring unusable retained UKI {image}: {error}",
                file=sys.stderr,
            )
    return candidates


def retained_uki_initrd(
    expected: dict[str, bytes], pristine: bytes, work: Path
) -> bytes | None:
    for image in retained_uki_candidates(work).get(expected[".cmdline"], []):
        # Verify a private snapshot, then reuse those exact bytes. The boot
        # partition can otherwise change between reading and sbverify.
        with tempfile.TemporaryDirectory(dir=work, prefix="retained-") as directory:
            snapshot = Path(directory) / "image.efi"
            try:
                check_staging_space(work, image.stat().st_size)
                shutil.copyfile(image, snapshot)
                verify_signature(snapshot)
                payload = PEImage.read(snapshot)
                if image.name != f"{uki_identifier(payload)}-uki.efi":
                    raise ValueError(
                        f"Retained UKI contents do not match their name: {image}"
                    )
                mismatch = payload_mismatch(payload, expected, skip=".initrd")
                if mismatch is not None:
                    raise ValueError(
                        f"Retained UKI payload mismatch: {image}: {mismatch}"
                    )
                initrd = payload.sections().get(".initrd")
                if (
                    initrd is None
                    or initrd[: len(pristine)] != pristine
                    or payload.header.sections[".initrd"].size != len(initrd)
                ):
                    raise ValueError(f"Retained UKI initrd mismatch: {image}")
                return bytes(initrd)
            except (OSError, ValueError, subprocess.CalledProcessError) as error:
                # A full staging filesystem is not a property of the image.
                if isinstance(error, OSError) and error.errno == errno.ENOSPC:
                    raise
                print(
                    f"warning: ignoring unusable retained UKI {image}: {error}",
                    file=sys.stderr,
                )
    return None


def stub_mismatch(payload: PEImage, stub: PEImage) -> str | None:
    if (payload.header.machine, payload.header.entrypoint) != (
        stub.header.machine,
        stub.header.entrypoint,
    ):
        return "UKI does not execute the selected systemd-stub"
    sections = payload.sections()
    for name, stub_contents in stub.sections().items():
        section = payload.header.sections.get(name)
        if name != ".sbat" and (
            sections.get(name) != stub_contents
            or section is None
            or section.size != stub.header.sections[name].size
        ):
            return f"UKI stub mismatch: {name}"
    return None


def reusable_installed_uki(
    expected: dict[str, bytes], work: Path, stub: PEImage, *, current_stub: bool
) -> Path | None:
    # Keep a verified image whose payload still matches, even if an older stub
    # built it, as Lanzaboote does: rollback keeps the stub a generation booted
    # with, and a stub update does not rewrite every retained generation. The
    # default generation always runs the selected stub.
    for image in retained_uki_candidates(work).get(expected[".cmdline"], []):
        try:
            payload = PEImage.read(image)
            if payload_mismatch(payload, expected) is not None:
                continue
            if current_stub:
                mismatch = stub_mismatch(payload, stub)
                if mismatch is not None:
                    raise ValueError(mismatch)
            elif payload.header.machine != stub.header.machine:
                raise ValueError("UKI is for another architecture")
            if image.name != f"{uki_identifier(payload)}-uki.efi":
                raise ValueError("contents do not match the name")
            verify_signature(image)
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            print(
                f"warning: not reusing installed UKI {image}: {error}",
                file=sys.stderr,
            )
            continue
        return image
    return None


def check_staging_space(work: Path, required: int) -> None:
    filesystem = os.statvfs(work)
    if required + 1024 * 1024 > filesystem.f_bavail * filesystem.f_frsize:
        raise OSError(
            errno.ENOSPC,
            "Insufficient UKI temporary staging space; set TMPDIR to a larger filesystem",
        )


def uki_boot_file(
    bootspec: BootSpec, work: Path, generation: int, *, critical: bool
) -> BootFile:
    # Stage images privately before publishing UKIs, entries or the default.
    directory = Path(tempfile.mkdtemp(dir=work))
    initrd = directory / "initrd"
    check_staging_space(work, bootspec.initrd.stat().st_size)
    shutil.copyfile(bootspec.initrd, initrd)
    secrets_failed = False
    if bootspec.initrdSecrets is not None:
        try:
            run([bootspec.initrdSecrets, initrd])
        except subprocess.CalledProcessError:
            if critical:
                raise
            secrets_failed = True

    cmdline = " ".join([f"init={bootspec.init}"] + bootspec.kernelParams).encode()
    cmdline_file = directory / "cmdline"
    cmdline_file.write_bytes(cmdline)
    os_release = bootspec.toplevel / "etc/os-release"
    uname = bootspec.uname.encode() if bootspec.uname is not None else None
    stub = Path(SYSTEMD) / f"lib/systemd/boot/efi/linux{UKI_CONFIG['efiArch']}.efi.stub"
    unsigned = directory / "unsigned.efi"
    command: list[str | Path] = [
        UKI_CONFIG["ukify"],
        "build",
        "--config=/dev/null",
        f"--efi-arch={UKI_CONFIG['efiArch']}",
        f"--stub={stub}",
        f"--linux={bootspec.kernel}",
        f"--initrd={initrd}",
        f"--cmdline=@{cmdline_file}",
        f"--os-release=@{os_release}",
        "--no-sign-kernel",
        "--no-measure",
        "--no-policy-digest",
        f"--output={unsigned}",
    ]
    expected = {
        ".linux": bootspec.kernel.read_bytes(),
        ".cmdline": cmdline,
        ".osrel": os_release.read_bytes(),
    }
    if uname is not None:
        command.append(f"--uname={uname.decode()}")
        expected[".uname"] = uname
    # Older bootspecs omit uname; let upstream ukify infer it from the kernel.
    if bootspec.devicetree is not None:
        command.append(f"--devicetree={bootspec.devicetree}")
        expected[".dtb"] = bootspec.devicetree.read_bytes()
    extra_sources: list[Path] = []
    extra_error = None
    for extra in bootspec.extraInitrdPaths:
        if extra.is_absolute() or ".." in extra.parts:
            extra_error = f"Extra initrd path must be boot-partition-relative: {extra}"
            break
        source = Path(
            bootspec.extraInitrdSources.get(str(extra), str(BOOT_MOUNT_POINT / extra))
        )
        if UKI_CONFIG["privateKey"] is not None and not source.resolve().is_relative_to(
            STORE_DIR
        ):
            extra_error = f"Signed UKI extra initrd requires an immutable extraFiles source: {extra}"
            break
        if not source.is_file():
            extra_error = f"Missing extra initrd archive: {source}"
            break
        extra_sources.append(source)
    if extra_error is not None and critical:
        raise ValueError(extra_error)
    retained = None
    if secrets_failed or extra_error is not None:
        retained = retained_uki_initrd(expected, bootspec.initrd.read_bytes(), work)
        # Unsigned migration may preserve legacy secrets. In signed mode an
        # unauthenticated legacy tail must never be promoted into a signed UKI.
        previous = None
        if bootspec.initrdSecrets is not None:
            previous = (
                BOOT_MOUNT_POINT
                / BootFile.from_initrd(
                    generation, bootspec.initrd, Path(bootspec.initrdSecrets)
                ).path
            )
        if retained is not None:
            initrd.write_bytes(retained)
        elif (
            UKI_CONFIG["privateKey"] is None
            and secrets_failed
            and previous is not None
            and previous.exists()
        ):
            if not previous.read_bytes().startswith(bootspec.initrd.read_bytes()):
                raise ValueError(f"Installed legacy initrd mismatch: {previous}")
            shutil.copyfile(previous, initrd)
        else:
            # Match the legacy non-default fallback, discarding any partial
            # output left by the failed appender.
            shutil.copyfile(bootspec.initrd, initrd)
        print(
            "warning: unavailable initrd inputs for an older "
            f"generation ({generation}): {extra_error or 'failed runtime secrets appender'}. Using its previous installed initrd "
            "if authenticated (or signing is disabled), otherwise its pristine initrd.",
            file=sys.stderr,
        )
    if retained is None and extra_error is None:
        with initrd.open("ab") as output:
            for source in extra_sources:
                # Linux permits concatenated, four-byte-aligned initramfs archives.
                output.write(b"\0" * (-output.tell() % 4))
                with source.open("rb") as input_file:
                    shutil.copyfileobj(input_file, output)
    expected[".initrd"] = initrd.read_bytes()
    stub_payload = PEImage.read(stub)
    reusable = reusable_installed_uki(
        expected, work, stub_payload, current_stub=critical
    )
    if reusable is not None:
        shutil.rmtree(directory)
        return BootFile(reusable.relative_to(BOOT_MOUNT_POINT), CopyWriter(reusable))
    # Reserve room for ukify output and, when signing, a second image. The
    # appender may grow the initrd; recheck its actual size before assembly.
    size = (
        sum(len(contents) for contents in expected.values())
        + stub.stat().st_size
        + 1024 * 1024
    )
    check_staging_space(work, size * (2 if UKI_CONFIG["privateKey"] is not None else 1))
    run(command)
    image = unsigned
    if UKI_CONFIG["privateKey"] is not None:
        image = directory / "signed.efi"
        run(
            [
                UKI_CONFIG["sbsign"],
                "--key",
                UKI_CONFIG["privateKey"],
                "--cert",
                UKI_CONFIG["certificate"],
                "--output",
                image,
                unsigned,
            ]
        )
    verify_signature(image)
    payload = PEImage.read(image)
    mismatch = stub_mismatch(payload, stub_payload)
    if mismatch is not None:
        raise ValueError(mismatch)
    mismatch = payload_mismatch(payload, expected)
    if mismatch is not None:
        raise ValueError(f"UKI payload mismatch: {mismatch}")
    identifier = uki_identifier(payload)
    relative = NIXOS_DIR / f"{identifier}-uki.efi"
    installed = BOOT_MOUNT_POINT / relative
    # A valid image with this identity was reused above, so a file here is
    # damaged. The name is the verified identity of the new image, so
    # publishing it over a corrupted or tampered file restores its contents.
    damaged = installed.exists()
    if damaged:
        print(f"warning: replacing damaged UKI {installed}", file=sys.stderr)
    # Keep only unique, new, verified images until publication. Reinstalling
    # retained generations no longer accumulates images or scratch initrds.
    staged = work / relative.name
    if not staged.exists():
        image.rename(staged)
    shutil.rmtree(directory)
    return BootFile(relative, CopyWriter(staged, replace=damaged))


def boot_file(
    profile: str | None,
    generation: int,
    specialisation: str | None,
    machine_id: str | None,
    bootspec: BootSpec,
    work: Path,
    *,
    critical: bool,
) -> tuple[BootFileList, str]:
    if specialisation:
        bootspec = bootspec.specialisations[specialisation]
    kernel = (
        uki_boot_file(bootspec, work, generation, critical=critical)
        if UKI_CONFIG["enable"]
        else BootFile.from_source(bootspec.kernel)
    )
    initrd = BootFile.from_initrd(
        generation,
        bootspec.initrd,
        Path(bootspec.initrdSecrets) if bootspec.initrdSecrets is not None else None,
    )
    devicetree = None
    if bootspec.devicetree is not None:
        devicetree = BootFile.from_source(bootspec.devicetree)

    kernel_params = " ".join([f"init={bootspec.init}"] + bootspec.kernelParams)
    build_time = int(system_dir(profile, generation, specialisation).stat().st_ctime)
    build_date = datetime.datetime.fromtimestamp(build_time).strftime("%F")

    title = "{name}{profile}{specialisation}".format(
        name=DISTRO_NAME,
        profile=" [" + profile + "]" if profile else "",
        specialisation=" (%s)" % specialisation if specialisation else "",
    )
    description = f"Generation {generation} {bootspec.label}, built on {build_date}"
    boot_entry = (
        [
            f"title {title}",
            f"version {description}",
        ]
        + (
            [f"uki /{kernel.path}"]
            if UKI_CONFIG["enable"]
            else [
                f"linux /{kernel.path}",
                f"initrd /{initrd.path}",
                *[f"initrd /{extra}" for extra in bootspec.extraInitrdPaths],
                f"options {kernel_params}",
            ]
        )
        + [
            f"machine-id {machine_id}" if machine_id is not None else None,
            f"devicetree /{devicetree.path}"
            if devicetree is not None and not UKI_CONFIG["enable"]
            else None,
            f"sort-key {bootspec.sortKey}",
        ]
    )
    contents = "\n".join(filter(None, boot_entry))
    entry, bootctl_id = BootFile.from_entry(contents.encode("utf-8"))
    return (
        [kernel, entry]
        if UKI_CONFIG["enable"]
        else list(filter(None, [kernel, initrd, devicetree, entry])),
        bootctl_id,
    )


def get_generations(
    profile: str | None = None, *, default_config: Path | None = None
) -> list[SystemIdentifier]:
    gen_list = run(
        [
            f"{NIX}/bin/nix-env",
            "--list-generations",
            "-p",
            "/nix/var/nix/profiles/%s"
            % ("system-profiles/" + profile if profile else "system"),
        ],
        stdout=subprocess.PIPE,
    ).stdout
    gen_lines = gen_list.split("\n")
    gen_lines.pop()

    configurationLimit = CONFIGURATION_LIMIT
    configurations = [
        SystemIdentifier(
            profile=profile, generation=int(line.split()[0]), specialisation=None
        )
        for line in gen_lines
    ]
    retained = configurations[-configurationLimit:]
    # The rollback target and the running system can lie outside the newest-N
    # window. Specialisations are separate closures, referenced from the root.
    booted = Path("/run/booted-system")
    protected = (
        {default_config, *([booted.resolve()] if booted.exists() else [])}
        if default_config is not None
        else set()
    )

    if protected:
        # Keep only the newest generation of each protected system.
        newest: dict[Path, SystemIdentifier] = {}
        for generation in configurations:
            directory = system_dir(profile, generation.generation, None)
            for target in [directory, *(directory / "specialisation").glob("*")]:
                if (resolved := target.resolve()) in protected:
                    newest[resolved] = generation
        kept = set(newest.values())
        # Make room by dropping the oldest unprotected generations; keep both
        # protected systems even if that exceeds the limit.
        droppable = [g for g in retained if g not in kept]
        for generation in [g for g in configurations if g in kept - set(retained)]:
            if configurationLimit > 0 and droppable:
                retained.remove(droppable.pop(0))
            retained.append(generation)
        retained.sort(key=lambda generation: generation.generation)
    return retained


def cleanup_esp() -> None:
    for path in (EFI_SYS_MOUNT_POINT / "loader" / "entries").glob("nixos*"):
        path.unlink()
    nixos_dir = EFI_SYS_MOUNT_POINT / NIXOS_DIR
    if nixos_dir.is_dir():
        shutil.rmtree(nixos_dir)


def get_profiles() -> list[str]:
    system_profiles = Path("/nix/var/nix/profiles/system-profiles/")
    if system_profiles.is_dir():
        return [
            x.name for x in system_profiles.iterdir() if not x.name.endswith("-link")
        ]
    else:
        return []


def install_bootloader(args: argparse.Namespace) -> None:
    with tempfile.TemporaryDirectory(prefix="systemd-boot-uki-") as directory:
        install_bootloader_staged(args, Path(directory))


def check_space(mount_point: Path, sizes: list[int], what: str) -> None:
    filesystem = os.statvfs(mount_point)
    cluster = filesystem.f_frsize
    required = 1024 * 1024  # Directory entries and filesystem metadata.
    for size in sizes:
        required += ((size + cluster - 1) // cluster + 1) * cluster
    if required > filesystem.f_bavail * cluster:
        raise OSError(errno.ENOSPC, f"Insufficient boot filesystem space for {what}")


def check_uki_space(
    boot_files: BootFileList, manager_updates: list[tuple[Path, Path]]
) -> None:
    # Replaced managers need room for a full temporary copy before rename.
    managers = [signed.stat().st_size for signed, _ in manager_updates]
    sizes: list[int] = []
    if EFI_SYS_MOUNT_POINT == BOOT_MOUNT_POINT:
        sizes += managers
    elif managers:
        check_space(EFI_SYS_MOUNT_POINT, managers, "signed boot managers")
    seen: set[Path] = set()
    for boot_file in boot_files:
        writer = boot_file.writer
        replace = isinstance(writer, CopyWriter) and writer.replace
        if boot_file.path in seen or (
            (BOOT_MOUNT_POINT / boot_file.path).exists() and not replace
        ):
            continue
        seen.add(boot_file.path)
        if isinstance(writer, CopyWriter):
            size = writer.source.stat().st_size
        elif isinstance(writer, ContentsWriter):
            size = len(writer.contents)
        else:
            raise TypeError("Unexpected UKI writer")
        sizes.append(size)
    check_space(BOOT_MOUNT_POINT, sizes, "staged UKIs")


def update_boot_manager() -> None:
    # flags to pass to bootctl install/update
    bootctl_flags = []

    if BOOT_MOUNT_POINT != EFI_SYS_MOUNT_POINT:
        bootctl_flags.append(f"--boot-path={BOOT_MOUNT_POINT}")

    if not CAN_TOUCH_EFI_VARIABLES:
        bootctl_flags.append("--variables=no")

    if GRACEFUL:
        bootctl_flags.append("--graceful")

    if os.getenv("NIXOS_INSTALL_BOOTLOADER") == "1":
        # bootctl uses fopen() with modes "wxe" and fails if the file exists.
        LOADER_CONF.unlink(missing_ok=True)

        run(
            [f"{SYSTEMD}/bin/bootctl", f"--esp-path={EFI_SYS_MOUNT_POINT}"]
            + bootctl_flags
            + ["install"]
        )
    else:
        # Let bootctl compare versions itself. Over Varlink, an already
        # current binary comes back as an io.systemd.System error carrying
        # ESTALE, which we can tell apart from real failures.
        params: dict[str, Any] = {"operation": "update"}
        if not CAN_TOUCH_EFI_VARIABLES:
            params["touchVariables"] = False
        if GRACEFUL:
            params["graceful"] = True
        reply = bootctl_varlink_call("io.systemd.BootControl.Install", params)

        error = reply.get("error")
        if error is not None:
            error_params = reply.get("parameters") or {}
            if (
                error == "io.systemd.System"
                and error_params.get("errno") == errno.ESTALE
            ):
                # Same or newer boot loader version already in place.
                pass
            else:
                raise RuntimeError(
                    f"bootctl update failed: {error} {json.dumps(error_params)}"
                )


def install_bootloader_staged(args: argparse.Namespace, work: Path) -> None:
    check_signing_inputs()
    manager_updates = (
        stage_signed_managers(work) if UKI_CONFIG["privateKey"] is not None else []
    )
    try:
        with open("/etc/machine-id") as machine_file:
            machine_id = machine_file.readlines()[0].strip()
    except IOError as e:
        if e.errno != errno.ENOENT:
            raise
        machine_id = None

    if os.getenv("NIXOS_INSTALL_GRUB") == "1":
        warnings.warn(
            "NIXOS_INSTALL_GRUB env var deprecated, use NIXOS_INSTALL_BOOTLOADER",
            DeprecationWarning,
        )
        os.environ["NIXOS_INSTALL_BOOTLOADER"] = "1"

    if not UKI_CONFIG["enable"]:
        update_boot_manager()

    LOADER_CONF.parent.mkdir(parents=True, exist_ok=True)
    (BOOT_MOUNT_POINT / NIXOS_DIR).mkdir(parents=True, exist_ok=True)
    (BOOT_MOUNT_POINT / "loader/entries").mkdir(parents=True, exist_ok=True)

    default_config = Path(args.default_config).resolve()
    requested = default_config if UKI_CONFIG["enable"] else None
    gens = get_generations(default_config=requested)
    for profile in get_profiles():
        gens += get_generations(profile, default_config=requested)

    if not gens:
        # With zero generations we would garbage-collect every kernel,
        # initrd and loader entry off the ESP, leaving the system
        # unbootable.
        print(
            "error: no system generations found in /nix/var/nix/profiles, "
            "refusing to remove all boot loader entries",
            file=sys.stderr,
        )
        sys.exit(1)

    boot_files: BootFileList = []
    critical_paths: set[Path] = set()

    default_entry_id: str | None = None

    specifications = [(gen, get_bootspec(gen.profile, gen.generation)) for gen in gens]
    if UKI_CONFIG["enable"] and not any(
        Path(spec.init).parent == default_config
        or any(
            Path(child.init).parent == default_config
            for child in spec.specialisations.values()
        )
        for _, spec in specifications
        if spec is not None
    ):
        raise ValueError(
            "Requested default configuration is not a bootable retained generation"
        )

    run([PREPARE_EXTRA_FILES])

    for gen, bootspec in specifications:
        if bootspec is None:
            continue
        is_default = Path(bootspec.init).parent == default_config
        new_boot_files, new_bootctl_id = boot_file(
            *gen, machine_id, bootspec, work, critical=is_default
        )
        boot_files.extend(new_boot_files)
        if is_default:
            default_entry_id = new_bootctl_id
            critical_paths.update(bf.path for bf in new_boot_files)
        for specialisation_name, specialisation in bootspec.specialisations.items():
            is_default = Path(specialisation.init).parent == default_config
            new_boot_files, new_bootctl_id = boot_file(
                gen.profile,
                gen.generation,
                specialisation_name,
                machine_id,
                bootspec,
                work,
                critical=is_default,
            )
            boot_files.extend(new_boot_files)
            if is_default:
                default_entry_id = new_bootctl_id
                critical_paths.update(bf.path for bf in new_boot_files)

    if UKI_CONFIG["enable"] and default_entry_id is None:
        raise ValueError(
            "Requested default generation has no usable bootspec; refusing UKI installation"
        )

    if UKI_CONFIG["enable"]:
        check_uki_space(boot_files, manager_updates)

    if UKI_CONFIG["enable"] and UKI_CONFIG["privateKey"] is None:
        update_boot_manager()
    install_signed_managers(manager_updates)

    # Garbage-collect stale kernels/initrds/entries before re-populating extra
    # files, so that user-supplied extraEntries (which may also live under
    # loader/entries and start with `nixos-`) are not removed again.
    if not UKI_CONFIG["enable"]:
        garbage_collect(boot_files)

    write_boot_files(boot_files, critical_paths)

    # FAT does not order metadata updates. Make new images and entries durable
    # before loader.conf names them, and that before old files are removed.
    if UKI_CONFIG["enable"]:
        sync_boot_filesystems(required=True)
    write_loader_conf(default_entry_id)

    if UKI_CONFIG["enable"]:
        sync_boot_filesystems(required=True)
        garbage_collect(boot_files)

    remove_extra_files()
    run([COPY_EXTRA_FILES])

    if BOOT_MOUNT_POINT != EFI_SYS_MOUNT_POINT:
        # Cleanup any entries in ESP if xbootldrMountPoint is set.
        # If the user later unsets xbootldrMountPoint, entries in XBOOTLDR will not be cleaned up
        # automatically, as we don't have information about the mount point anymore.
        cleanup_esp()


def remove_extra_files() -> None:
    extra_files_dir = BOOT_MOUNT_POINT / NIXOS_DIR / ".extra-files"
    for root, _, files in extra_files_dir.walk(top_down=False):
        relative_root = root.relative_to(extra_files_dir)
        actual_root = BOOT_MOUNT_POINT / relative_root

        for file in files:
            actual_file = actual_root / file
            actual_file.unlink(missing_ok=True)
            (root / file).unlink()

        if not list(actual_root.iterdir()):
            actual_root.rmdir()
        root.rmdir()

    extra_files_dir.mkdir(parents=True, exist_ok=True)


def garbage_collect(gc_roots: BootFileList) -> None:
    keep = {BOOT_MOUNT_POINT / gc_root.path for gc_root in gc_roots}

    def delete_path(e: os.DirEntry) -> None:
        if e.is_file(follow_symlinks=True) and Path(e.path) not in keep:
            os.remove(e.path)

    for e in os.scandir(BOOT_MOUNT_POINT / NIXOS_DIR):
        delete_path(e)

    for e in os.scandir(BOOT_MOUNT_POINT / "loader" / "entries"):
        match = re.fullmatch(r"nixos-.+\.conf", e.name)
        if match:
            delete_path(e)


def sync_boot_filesystems(*, required: bool) -> None:
    for mount_point in dict.fromkeys((BOOT_MOUNT_POINT, EFI_SYS_MOUNT_POINT)):
        fd = os.open(mount_point, os.O_RDONLY)
        try:
            if libc.syncfs(fd) == 0:
                continue
            error = ctypes.get_errno()
        finally:
            os.close(fd)
        if required:
            raise OSError(error, f"Could not sync {mount_point}", str(mount_point))
        print(f"could not sync {mount_point}: {os.strerror(error)}", file=sys.stderr)


def write_boot_files(boot_files: BootFileList, critical_paths: set[Path]) -> None:
    # Deduplicate by destination path so shared files are written once.
    seen: set[Path] = set()
    for boot_file in boot_files:
        if boot_file.path in seen:
            continue
        seen.add(boot_file.path)
        boot_file.writer.write_boot_file(
            BOOT_MOUNT_POINT / boot_file.path,
            critical=boot_file.path in critical_paths,
        )


def main() -> None:
    parser = argparse.ArgumentParser(
        description=f"Update {DISTRO_NAME}-related systemd-boot files"
    )
    parser.add_argument(
        "default_config",
        metavar="DEFAULT-CONFIG",
        help=f"The default {DISTRO_NAME} config to boot",
    )
    args = parser.parse_args()

    run([CHECK_MOUNTPOINTS])

    try:
        install_bootloader(args)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f"error: {error}", file=sys.stderr)
        sys.exit(1)
    finally:
        # Since fat32 provides little recovery facilities after a crash,
        # it can leave the system in an unbootable state, when a crash/outage
        # happens shortly after an update. To decrease the likelihood of this
        # event sync the efi filesystem after each update.
        sync_boot_filesystems(required=False)


if __name__ == "__main__":
    main()
