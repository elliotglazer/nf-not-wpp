#!/usr/bin/env python3
"""Portable launcher for the hash-pinned nominal Metamath translator v3.

The historical v1/v2/v3 sources remain byte-exact under ``archive/``. This
launcher changes only two execution-environment policies that were useful
during development but are unsuitable for a published repository:

* accept any CPython 3.12 interpreter instead of one Windows executable hash;
* relocate paths embedded in historical receipts at their canonical
  ``work/`` component into this checkout's ``translation/archive`` tree.

Every historical translator module and every static/runtime input retains its
original SHA-256 check. The launcher remains source-only and never invokes
Lean. Generated receipts identify this launcher as their producer.
"""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path, PurePosixPath
import sys
from types import ModuleType
from typing import Any, Sequence


HERE = Path(__file__).resolve().parent
THIS = Path(__file__).resolve()


def extended_path(path: Path) -> Path:
    """Use Win32's extended path form when a checkout has a long prefix."""

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
    require(path.is_file(), f"missing pinned translator module: {path}")
    actual = sha256(path)
    require(actual == expected, f"pinned translator hash mismatch: {actual}")
    require(name not in sys.modules, f"translator module already loaded: {name}")
    spec = importlib.util.spec_from_file_location(name, path)
    require(
        spec is not None and spec.loader is not None,
        f"could not load pinned translator module: {path}",
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def checkout_path(value: str | Path) -> Path:
    """Map a historical receipt path to this checkout's archived work tree."""

    portable = str(value).replace("\\", "/")
    if portable.startswith("work/"):
        relative = portable
    elif "/work/" in portable:
        relative = "work/" + portable.split("/work/", 1)[1]
    else:
        path = Path(value)
        if path.is_absolute():
            return path.resolve()
        return (ARCHIVE_WORKSPACE / path).resolve()
    result = ARCHIVE_WORKSPACE.joinpath(*PurePosixPath(relative).parts).resolve()
    try:
        result.relative_to(ARCHIVE_WORKSPACE.resolve())
    except ValueError as error:
        raise RuntimeError(f"receipt path escapes archive: {value}") from error
    return result


def patch_alpha_paths(module: ModuleType, seen: set[int] | None = None) -> None:
    if seen is None:
        seen = set()
    if id(module) in seen:
        return
    seen.add(id(module))
    if hasattr(module, "_workspace_path"):
        module._workspace_path = checkout_path
    for child_name in ("legacy", "base"):
        child = getattr(module, child_name, None)
        if isinstance(child, ModuleType):
            patch_alpha_paths(child, seen)


def install_checkout_relocation(translator: ModuleType) -> None:
    translator._workspace_resource_path = checkout_path

    def resource_relative_path(
        value: Any, resource: Path, description: str
    ) -> Path:
        translator.require(
            isinstance(value, str) and value,
            f"predecessor resource has no {description} path",
        )
        portable = value.replace("\\", "/")
        path = Path(value)
        if (
            path.is_absolute()
            or portable.startswith("work/")
            or "/work/" in portable
        ):
            return checkout_path(value)
        return (resource.parent / path).resolve()

    translator.resource_relative_path = resource_relative_path
    original_load_backend = translator.load_backend

    def load_backend(profile_id: str = "WPP_PROFILE_V1") -> Any:
        backend = original_load_backend(profile_id)
        patch_alpha_paths(backend.alpha_core)
        return backend

    translator.load_backend = load_backend


def load_v1() -> ModuleType:
    return load_exact(
        TRANSLATOR_V1,
        TRANSLATOR_V1_SHA256,
        "_portable_nominal_mm_translator_v1_pinned",
    )


def load_v2() -> ModuleType:
    module = load_exact(
        TRANSLATOR_V2,
        TRANSLATOR_V2_SHA256,
        "_portable_nominal_mm_translator_v2_pinned",
    )
    module.load_predecessor = load_v1
    original_install = module.install_identity_expander

    def install_identity_expander(translator: ModuleType) -> None:
        original_install(translator)
        install_checkout_relocation(translator)

    module.install_identity_expander = install_identity_expander
    return module


def main(argv: Sequence[str] | None = None) -> int:
    require(
        sys.implementation.name == "cpython" and sys.version_info[:2] == (3, 12),
        "portable translator requires CPython 3.12.x",
    )
    translator_v3 = load_exact(
        TRANSLATOR_V3,
        TRANSLATOR_V3_SHA256,
        "_portable_nominal_mm_translator_v3_pinned",
    )
    translator_v3.load_predecessor = load_v2
    translator_v3.THIS = THIS
    return int(translator_v3.main(argv))


if __name__ == "__main__":
    raise SystemExit(main())
