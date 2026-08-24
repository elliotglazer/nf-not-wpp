#!/usr/bin/env python3
"""Portable, source-only launcher using textual compiled-evidence receipts.

This successor preserves the hash-pinned historical translator stack and the
portable v1 relocation policy.  Historical ``.olean`` files are represented
only by a checked textual ledger: the translator validates their archived
path/size/SHA-256 contracts and the hash-bearing JSON authority for every
entry, but never opens or requires a compiled Lean artifact.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys
from types import ModuleType
from typing import Any, Mapping, Sequence


HERE = Path(__file__).resolve().parent
THIS = Path(__file__).resolve()


def extended_path(path: Path) -> Path:
    resolved = path.resolve()
    raw = str(resolved)
    if sys.platform == "win32" and not raw.startswith("\\\\?\\"):
        return Path("\\\\?\\" + raw)
    return resolved


ARCHIVE_WORKSPACE = extended_path(HERE / "archive")
TRANSLATOR_DIR = (
    ARCHIVE_WORKSPACE
    / "work"
    / "nf_choice_clean_fol_2026-08-21"
    / "direct_nominal_prf_001"
)
PORTABLE_V1 = HERE / "portable_nominal_mm_translator_v1.py"
PORTABLE_V1_SHA256 = (
    "08ADD9D39ED23E1E755EB59E12673FABD6AA0CCDB5A02C76452CC58E6E8853B6"
)
TRANSLATOR_V1 = TRANSLATOR_DIR / "reusable_nominal_mm_translator_v1.py"
TRANSLATOR_V1_SHA256 = (
    "8ABE386FEC8BEE78499D25B3B488C4C81054019590789CC1AF71D4DC352F3A94"
)
TRANSLATOR_V2 = TRANSLATOR_DIR / "reusable_nominal_mm_translator_v2.py"
TRANSLATOR_V2_SHA256 = (
    "52ED85A33329D1D4CE0E9D05622F74917E1CD9662959AAD7D7B6175244F34615"
)
TRANSLATOR_V3 = TRANSLATOR_DIR / "reusable_nominal_mm_translator_v3.py"
TRANSLATOR_V3_SHA256 = (
    "DECC5089EAB55B95806EB74742FD47A1EB127502B243811DD882737FCB98475F"
)
EVIDENCE_LEDGER = ARCHIVE_WORKSPACE / "compiled_lean_evidence.json"
EVIDENCE_LEDGER_SHA256 = (
    "17532DD6BEBD20E3C45F110EE7CACAA1A69CFCB9784DB6E40CF0C30C40D224BD"
)
EVIDENCE_CONTRACT_SET_SHA256 = (
    "859A4B86E3FEA2FCA57AB4EFA09B74ED06C04CBFEBB0D6D8D5AB055F42972AE4"
)

SHA256_RE = re.compile(r"^[0-9A-F]{64}$")
EXPECTED_ENTRY_COUNT = 79
EXPECTED_ALPHA_COUNT = 77
EXPECTED_WPP_COUNT = 2
EXPECTED_TOTAL_BYTES = 21_417_512


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def load_exact(path: Path, expected: str, name: str) -> ModuleType:
    require(path.is_file(), f"missing pinned Python module: {path}")
    actual = sha256(path)
    require(actual == expected, f"pinned Python module hash mismatch: {actual}")
    require(name not in sys.modules, f"Python module already loaded: {name}")
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None,
            f"could not load pinned Python module: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def normalize_historical_path(value: str) -> str | None:
    portable = value.replace("\\", "/")
    if portable.startswith("work/"):
        return portable
    marker = "/work/"
    if marker in portable:
        return "work/" + portable.split(marker, 1)[1]
    return None


def archive_path(relative: str) -> Path:
    pure = PurePosixPath(relative)
    require(
        not pure.is_absolute()
        and all(part not in {"", ".", ".."} for part in pure.parts)
        and "\\" not in relative
        and ":" not in relative,
        f"invalid archived path: {relative!r}",
    )
    result = ARCHIVE_WORKSPACE.joinpath(*pure.parts).resolve()
    require(result.is_relative_to(ARCHIVE_WORKSPACE.resolve()),
            f"archived path escapes archive: {relative!r}")
    return result


def json_pointer(document: Any, pointer: str) -> Any:
    require(isinstance(pointer, str) and pointer.startswith("/"),
            f"invalid JSON pointer: {pointer!r}")
    current = document
    for encoded in pointer[1:].split("/"):
        token = encoded.replace("~1", "/").replace("~0", "~")
        if isinstance(current, list):
            require(token.isdigit(), f"invalid JSON array pointer: {pointer}")
            index = int(token)
            require(0 <= index < len(current), f"JSON pointer out of range: {pointer}")
            current = current[index]
        else:
            require(isinstance(current, Mapping) and token in current,
                    f"missing JSON pointer: {pointer}")
            current = current[token]
    return current


def path_key(path: str | Path) -> str:
    resolved = str(Path(path).resolve())
    return os.path.normcase(resolved) if sys.platform == "win32" else resolved


_CONTRACTS: dict[str, dict[str, Any]] = {}


def load_evidence_ledger() -> None:
    require(sha256(EVIDENCE_LEDGER) == EVIDENCE_LEDGER_SHA256,
            "compiled Lean textual-evidence ledger hash mismatch")
    data = json.loads(EVIDENCE_LEDGER.read_text(encoding="utf-8"))
    require(isinstance(data, dict), "compiled Lean evidence ledger is not an object")
    require(
        data.get("schema") == "nf-wpp-compiled-lean-textual-evidence-v1"
        and data.get("status") == "FROZEN_TEXTUAL_CERTIFICATE_LEDGER"
        and data.get("binaryArtifactsRequiredAtTranslationTime") is False,
        "compiled Lean evidence ledger contract changed",
    )
    entries = data.get("entries")
    require(isinstance(entries, list), "compiled Lean evidence entries are missing")
    require(
        data.get("entryCount") == len(entries) == EXPECTED_ENTRY_COUNT
        and data.get("alphaCertificateCount") == EXPECTED_ALPHA_COUNT
        and data.get("wppProfileCertificateCount") == EXPECTED_WPP_COUNT
        and data.get("totalHistoricalBytes") == EXPECTED_TOTAL_BYTES
        and data.get("contractSetSha256") == EVIDENCE_CONTRACT_SET_SHA256,
        "compiled Lean evidence census changed",
    )

    receipt_cache: dict[Path, Any] = {}
    contract_lines: list[str] = []
    paths: list[str] = []
    category_counts = {
        "alpha-certificate": 0,
        "wpp-profile-certificate": 0,
    }
    contracts: dict[str, dict[str, Any]] = {}
    for index, entry in enumerate(entries, start=1):
        require(isinstance(entry, Mapping), f"invalid evidence entry {index}")
        category = entry.get("category")
        require(category in category_counts, f"invalid evidence category at {index}")
        category_counts[str(category)] += 1
        relative = entry.get("path")
        size = entry.get("bytes")
        digest = entry.get("sha256")
        require(
            isinstance(relative, str) and relative.endswith(".olean")
            and isinstance(size, int) and not isinstance(size, bool) and size > 0
            and isinstance(digest, str) and SHA256_RE.fullmatch(digest) is not None,
            f"invalid compiled Lean contract at entry {index}",
        )
        absolute = archive_path(relative)
        key = path_key(absolute)
        require(key not in contracts, f"duplicate compiled Lean contract: {relative}")

        authority = entry.get("authority")
        require(isinstance(authority, Mapping), f"missing authority at entry {index}")
        receipt_relative = authority.get("receipt")
        receipt_digest = authority.get("receiptSha256")
        require(
            isinstance(receipt_relative, str)
            and isinstance(receipt_digest, str)
            and SHA256_RE.fullmatch(receipt_digest) is not None,
            f"invalid authority identity at entry {index}",
        )
        receipt = archive_path(receipt_relative)
        require(receipt.suffix.lower() == ".json" and receipt.is_file(),
                f"missing textual authority: {receipt}")
        require(sha256(receipt) == receipt_digest,
                f"textual authority hash mismatch: {receipt_relative}")
        if receipt not in receipt_cache:
            receipt_cache[receipt] = json.loads(receipt.read_text(encoding="utf-8"))
        document = receipt_cache[receipt]
        authority_path = json_pointer(document, authority.get("pathPointer"))
        authority_digest = json_pointer(document, authority.get("sha256Pointer"))
        require(
            isinstance(authority_path, str)
            and normalize_historical_path(authority_path) == relative
            and isinstance(authority_digest, str)
            and authority_digest.upper() == digest,
            f"textual authority does not certify entry {index}",
        )
        bytes_pointer = authority.get("bytesPointer")
        if bytes_pointer is not None:
            require(json_pointer(document, bytes_pointer) == size,
                    f"textual authority byte count differs at entry {index}")

        contract = {
            "path": relative,
            "bytes": size,
            "sha256": digest,
            "category": category,
        }
        contracts[key] = contract
        paths.append(relative)
        contract_lines.append(f"{relative}\t{size}\t{digest}\n")

    require(paths == sorted(paths), "compiled Lean evidence paths are not ordered")
    require(
        category_counts["alpha-certificate"] == EXPECTED_ALPHA_COUNT
        and category_counts["wpp-profile-certificate"] == EXPECTED_WPP_COUNT,
        "compiled Lean evidence category census changed",
    )
    actual_set = hashlib.sha256("".join(contract_lines).encode("utf-8")).hexdigest().upper()
    require(actual_set == EVIDENCE_CONTRACT_SET_SHA256,
            "compiled Lean evidence contract-set hash mismatch")
    _CONTRACTS.clear()
    _CONTRACTS.update(contracts)


def evidence_contract(path: str | Path) -> dict[str, Any] | None:
    return _CONTRACTS.get(path_key(path))


_NativePath = type(Path())


class ReceiptPath(_NativePath):
    """Path whose archived ``.olean`` identity is supplied by the ledger."""

    def is_file(self) -> bool:
        if evidence_contract(self) is not None:
            return True
        return super().is_file()

    def stat(self, *, follow_symlinks: bool = True) -> os.stat_result:
        contract = evidence_contract(self)
        if contract is not None:
            values = [0] * 10
            values[6] = int(contract["bytes"])
            return os.stat_result(values)
        return super().stat(follow_symlinks=follow_symlinks)

    def open(self, *args: Any, **kwargs: Any) -> Any:
        if evidence_contract(self) is not None:
            raise RuntimeError(
                f"compiled Lean binary access is forbidden; textual receipt used: {self}"
            )
        return super().open(*args, **kwargs)


def receipt_checkout_path(value: str | Path) -> ReceiptPath:
    portable = str(value).replace("\\", "/")
    if portable.startswith("work/"):
        relative = portable
    elif "/work/" in portable:
        relative = "work/" + portable.split("/work/", 1)[1]
    else:
        path = Path(value)
        if path.is_absolute():
            return ReceiptPath(str(path.resolve()))
        return ReceiptPath(str((ARCHIVE_WORKSPACE / path).resolve()))
    return ReceiptPath(str(archive_path(relative)))


def install_alpha_receipts(module: ModuleType, seen: set[int] | None = None) -> None:
    if seen is None:
        seen = set()
    if id(module) in seen:
        return
    seen.add(id(module))
    if not getattr(module, "_textual_olean_receipts_installed", False):
        original_sha256 = module.sha256

        def receipt_sha256(path: Path) -> str:
            contract = evidence_contract(path)
            return str(contract["sha256"]) if contract is not None else original_sha256(path)

        module.sha256 = receipt_sha256
        module.Path = ReceiptPath
        if hasattr(module, "_workspace_path"):
            module._workspace_path = receipt_checkout_path
        module._textual_olean_receipts_installed = True
    for child_name in ("legacy", "base"):
        child = getattr(module, child_name, None)
        if isinstance(child, ModuleType):
            install_alpha_receipts(child, seen)


def install_wpp_profile_receipts(module: ModuleType) -> None:
    if getattr(module, "_textual_olean_receipts_installed", False):
        return
    original_sha256_file = module.sha256_file
    original_require_sha256 = module.require_sha256

    def receipt_sha256_file(path: Path) -> str:
        contract = evidence_contract(path)
        return (
            str(contract["sha256"])
            if contract is not None
            else original_sha256_file(path)
        )

    def require_sha256(path: Path, expected: str, description: str) -> None:
        contract = evidence_contract(path)
        if contract is None:
            original_require_sha256(path, expected, description)
            return
        require(
            contract["category"] == "wpp-profile-certificate"
            and contract["sha256"] == expected,
            f"WPP textual compiled-evidence contract mismatch: {description}",
        )

    module.sha256_file = receipt_sha256_file
    module.require_sha256 = require_sha256
    module._textual_olean_receipts_installed = True


def install_textual_evidence(translator: ModuleType) -> None:
    original_sha256 = translator.sha256

    def receipt_sha256(path: Path) -> str:
        contract = evidence_contract(path)
        return str(contract["sha256"]) if contract is not None else original_sha256(path)

    translator.sha256 = receipt_sha256
    translator.Path = ReceiptPath
    translator._workspace_resource_path = receipt_checkout_path

    original_verify_profile = translator.verify_wpp_profile_manifest

    def verify_wpp_profile_manifest(
        manifest_path: Path,
        expected_sha256: str,
        roots: Mapping[str, Path] | None = None,
        *,
        profile_id: str = "WPP_PROFILE_V1",
    ) -> dict[str, Any]:
        selected_roots = (
            {key: ReceiptPath(str(value)) for key, value in roots.items()}
            if roots is not None
            else {"workspace": ReceiptPath(str(ARCHIVE_WORKSPACE))}
        )
        return original_verify_profile(
            manifest_path,
            expected_sha256,
            selected_roots,
            profile_id=profile_id,
        )

    translator.verify_wpp_profile_manifest = verify_wpp_profile_manifest
    original_load_backend = translator.load_backend

    def load_backend(profile_id: str = "WPP_PROFILE_V1") -> Any:
        backend = original_load_backend(profile_id)
        install_alpha_receipts(backend.alpha_core)
        install_wpp_profile_receipts(backend.wpp_config)
        return backend

    translator.load_backend = load_backend


def main(argv: Sequence[str] | None = None) -> int:
    require(
        sys.implementation.name == "cpython" and sys.version_info[:2] == (3, 12),
        "portable translator requires CPython 3.12.x",
    )
    load_evidence_ledger()
    portable_v1 = load_exact(
        PORTABLE_V1,
        PORTABLE_V1_SHA256,
        "_portable_nominal_mm_translator_v1_for_textual_v2",
    )

    def load_historical_v1() -> ModuleType:
        return load_exact(
            TRANSLATOR_V1,
            TRANSLATOR_V1_SHA256,
            "_portable_textual_nominal_mm_translator_v1_pinned",
        )

    def load_historical_v2() -> ModuleType:
        module = load_exact(
            TRANSLATOR_V2,
            TRANSLATOR_V2_SHA256,
            "_portable_textual_nominal_mm_translator_v2_pinned",
        )
        module.load_predecessor = load_historical_v1
        original_install = module.install_identity_expander

        def install_identity_expander(translator: ModuleType) -> None:
            original_install(translator)
            portable_v1.install_checkout_relocation(translator)
            install_textual_evidence(translator)

        module.install_identity_expander = install_identity_expander
        return module

    translator_v3 = load_exact(
        TRANSLATOR_V3,
        TRANSLATOR_V3_SHA256,
        "_portable_textual_nominal_mm_translator_v3_pinned",
    )
    translator_v3.load_predecessor = load_historical_v2
    translator_v3.THIS = THIS
    return int(translator_v3.main(argv))


if __name__ == "__main__":
    raise SystemExit(main())
