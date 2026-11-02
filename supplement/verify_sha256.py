from pathlib import Path
import hashlib
root=Path(__file__).resolve().parent
rows=(root/'SHA256SUMS.txt').read_text(encoding='utf-8').splitlines()
for row in rows:
    expected,name=row.split('  ',1)
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,name
print('PASS:',len(rows),'files')
