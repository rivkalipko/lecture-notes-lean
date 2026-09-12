"""Reject proof escape hatches and modules omitted from the default build."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
sources = sorted((root / "LectureNotes").rglob("*.lean"))
imports = set(re.findall(r"^import (\S+)", (root / "LectureNotes.lean").read_text(), re.M))
for path in sources:
    text = path.read_text()
    # Deliberately scan comments too: the project source needs no placeholder tokens.
    banned = re.search(r"\b(sorry|admit|axiom|sorryAx|native_decide|implemented_by|unsafe)\b", text)
    if banned:
        raise SystemExit(f"Forbidden source token {banned.group()} in {path.relative_to(root)}")
    module = ".".join(path.relative_to(root).with_suffix("").parts)
    if module not in imports:
        raise SystemExit(f"Module missing from root imports: {module}")
print(f"Source audit passed: {len(sources)} modules, all imported, no forbidden tokens.")
