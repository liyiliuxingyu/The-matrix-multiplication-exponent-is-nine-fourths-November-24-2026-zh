"""核对随包发布文件。"""
from hashlib import sha256
from pathlib import Path
import sys

root = Path(__file__).resolve().parent
errors = []
for record in (root / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
    expected, filename = record.split("  ", 1)
    path = root / filename
    if not path.is_file() or sha256(path.read_bytes()).hexdigest() != expected:
        errors.append(filename)
if errors:
    sys.exit("下列文件与发布清单不符：\n" + "\n".join(errors))
print("所有随包发布文件的 SHA-256 与清单相符。")
