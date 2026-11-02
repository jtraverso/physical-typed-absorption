"""Check this package against the SHA-256 list of the published Paper III source archive.

The archive's top-level README.md, lakefile.toml, source_closure.json and verify_sha256.py are
kept in supplement/; every other listed file is at the same path as in the archive.
"""
from pathlib import Path
import hashlib

root = Path(__file__).resolve().parent
moved = {"README.md", "lakefile.toml", "source_closure.json", "verify_sha256.py"}
rows = (root / "supplement" / "SHA256SUMS.txt").read_text(encoding="utf-8").splitlines()
for row in rows:
    expected, name = row.split("  ", 1)
    path = root / "supplement" / name if name in moved else root / name
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, name
print("PASS:", len(rows), "files")
