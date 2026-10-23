"""Check that the solution article covers current exercise files and inventory."""

import json
import re
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
ENTRY = re.compile(r'<a id="(r\d{2}e\d{2})"></a>')


def validate(root=ROOT):
    """Return structural errors; mathematical accuracy needs source review."""
    article = root / "docs/rudin/solutions.md"
    text = article.read_text()
    data = json.loads((root / "exercises.json").read_text())
    records = {e["id"].lower(): e for e in data["exercises"]}
    sources = {
        f"r{int(p.parent.name[7:]):02}e{int(p.stem[8:]):02}": p
        for p in (root / "Math/Rudin").glob("Chapter*/Exercise*.lean")
    }
    matches = list(ENTRY.finditer(text))
    ids = [m[1] for m in matches]
    errors = []

    def require(condition, message):
        if not condition:
            errors.append(message)

    require(len(ids) == len(set(ids)), "Duplicate exercise entries")
    require(ids == sorted(ids), "Exercise entries are not in source order")
    require(set(ids) == set(sources),
            f"Exercise coverage differs: missing={sorted(sources.keys() - set(ids))}, "
            f"extra={sorted(set(ids) - sources.keys())}")
    require(f"**{len(sources)} exercise files**" in text, "Stale exercise-file count")
    verified = [e for e in records.values() if all(o["status"] == "verified" for o in e["obligations"])]
    corrected = sum(e["disposition"] == "refuted_and_corrected" for e in verified)
    require(f"**{len(verified)} verified resolutions**" in text, "Stale verified-resolution count")
    require(f"**{len(sources) - len(verified)} entries**" in text, "Stale pending-entry count")
    require(f"{len(verified) - corrected} proved as stated" in text, "Stale as-stated count")
    require("docs/rudin/solutions.md" in (root / "README.md").read_text(), "README link missing")

    for i, match in enumerate(matches):
        eid = match[1]
        if eid not in records or eid not in sources:
            continue
        body = text[match.end():matches[i + 1].start() if i + 1 < len(matches) else len(text)]
        record, source = records[eid], sources[eid]
        require(f"../../{source.relative_to(root).as_posix()}" in body, f"{eid}: source link missing")
        require(re.search(rf'^### {record["chapter"]}\.{record["number"]}\s', body, re.M),
                f"{eid}: incorrect exercise heading")
        for label in ("**Statement.**", "**Proof.**", "**Lean declarations:**"):
            require(label in body, f"{eid}: missing {label}")
        is_verified = all(o["status"] == "verified" for o in record["obligations"])
        status = "Pending verification."
        if is_verified:
            status = "Verified as stated." if record["disposition"] == "as_stated" else "Verified refutation and correction."
        require(f"**Inventory status:** {status}" in body, f"{eid}: stale inventory status")
        metadata = re.search(r"\*\*Lean declarations:\*\*(.*?)(?:\n\n|\Z)", body, re.S)
        names = re.findall(r"`([^`]+)`", metadata[1]) if metadata else []
        short_names = {name.split(".")[-1] for name in names}
        for obligation in record["obligations"]:
            for name in obligation["declarations"]:
                require(name.split(".")[-1] in short_names, f"{eid}: missing mapped declaration {name}")
        source_names = set(re.findall(r"\b(?:theorem|lemma|def|abbrev|structure|alias)\s+([\w.']+)", source.read_text()))
        for name in short_names:
            require(name in source_names or any(n.endswith("." + name) for n in source_names),
                    f"{eid}: unknown source declaration {name}")

    anchors = re.findall(r'<a id="([^"]+)"></a>', text)
    require(len(anchors) == len(set(anchors)), "Duplicate article anchors")
    for href in re.findall(r"\]\(([^\s)]+)\)", text):
        url = urlsplit(href)
        if url.scheme or url.netloc:
            continue
        if url.path:
            require((article.parent / unquote(url.path)).is_file(), f"Broken file link: {href}")
        elif url.fragment:
            require(unquote(url.fragment) in anchors, f"Broken article anchor: {href}")
    require(not re.search(r"\b(?:TODO|TBD|FIXME)\b", text), "Editorial placeholder")
    require("[Showing lines " not in text and "more lines in file. Use offset=" not in text,
            "Truncated tool output in article")
    return errors


def main():
    errors = validate()
    if errors:
        raise SystemExit("Solution article check failed:\n" + "\n".join(errors))
    print("Solution article coverage, statuses, declarations, and links passed.")


if __name__ == "__main__":
    main()
