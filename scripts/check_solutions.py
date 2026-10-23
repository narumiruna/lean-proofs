"""Check that the solution article covers current exercise files and inventory."""

import json
import os
import re
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
ENTRY = re.compile(r'<a id="(r\d{2}e\d{2})"></a>')


def validate(root=ROOT):
    """Return structural errors; mathematical accuracy needs source review."""
    article = root / "docs/rudin/solutions.md"
    index_text = article.read_text()
    chapters = sorted((article.parent / "solutions").glob("chapter-*.md"))
    documents = {article: index_text, **{path: path.read_text() for path in chapters}}
    entries = []
    for path in chapters:
        content = documents[path]
        matches = list(ENTRY.finditer(content))
        for i, match in enumerate(matches):
            end = matches[i + 1].start() if i + 1 < len(matches) else len(content)
            entries.append((match[1], content[match.end():end], path))
    data = json.loads((root / "exercises.json").read_text())
    records = {e["id"].lower(): e for e in data["exercises"]}
    sources = {
        f"r{int(p.parent.name[7:]):02}e{int(p.stem[8:]):02}": p
        for p in (root / "Math/Rudin").glob("Chapter*/Exercise*.lean")
    }
    ids = [eid for eid, _, _ in entries]
    errors = []

    def require(condition, message):
        if not condition:
            errors.append(message)

    require(len(ids) == len(set(ids)), "Duplicate exercise entries")
    require(ids == sorted(ids), "Exercise entries are not in source order")
    require(set(ids) == set(sources),
            f"Exercise coverage differs: missing={sorted(sources.keys() - set(ids))}, "
            f"extra={sorted(set(ids) - sources.keys())}")
    expected_chapters = {eid[1:3] for eid in sources}
    require({path.stem.removeprefix("chapter-") for path in chapters} == expected_chapters,
            "Chapter files differ from exercise sources")
    require(not ENTRY.search(index_text), "Exercise content belongs in chapter files, not the index")
    for number in sorted(expected_chapters):
        require(f"solutions/chapter-{number}.md#chapter-{number}" in index_text,
                f"Chapter {number}: index link missing")
    require(f"**{len(sources)} exercise files**" in index_text, "Stale exercise-file count")
    verified = [e for e in records.values() if all(o["status"] == "verified" for o in e["obligations"])]
    corrected = sum(e["disposition"] == "refuted_and_corrected" for e in verified)
    require(f"**{len(verified)} verified resolutions**" in index_text, "Stale verified-resolution count")
    require(f"**{len(sources) - len(verified)} entries**" in index_text, "Stale pending-entry count")
    require(f"{len(verified) - corrected} proved as stated" in index_text, "Stale as-stated count")
    require("docs/rudin/solutions.md" in (root / "README.md").read_text(), "README link missing")

    for eid, body, owner in entries:
        require(owner.name == f"chapter-{eid[1:3]}.md", f"{eid}: wrong chapter file")
        if eid not in records or eid not in sources:
            continue
        record, source = records[eid], sources[eid]
        require(os.path.relpath(source, owner.parent) in body, f"{eid}: source link missing")
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

    for path, content in documents.items():
        anchors = re.findall(r'<a id="([^"]+)"></a>', content)
        require(len(anchors) == len(set(anchors)), f"{path.name}: duplicate article anchors")
        for href in re.findall(r"\]\(([^\s)]+)\)", content):
            url = urlsplit(href)
            if url.scheme or url.netloc:
                continue
            target = (path.parent / unquote(url.path)).resolve() if url.path else path.resolve()
            require(target.is_file(), f"Broken file link: {href}")
            if url.fragment and target.is_file():
                target_anchors = re.findall(r'<a id="([^"]+)"></a>', target.read_text())
                require(unquote(url.fragment) in target_anchors, f"Broken article anchor: {href}")
        require(not re.search(r"\b(?:TODO|TBD|FIXME)\b", content), "Editorial placeholder")
        require("[Showing lines " not in content and "more lines in file. Use offset=" not in content,
                "Truncated tool output in article")
    return errors


def main():
    errors = validate()
    if errors:
        raise SystemExit("Solution article check failed:\n" + "\n".join(errors))
    print("Solution article coverage, statuses, declarations, and links passed.")


if __name__ == "__main__":
    main()
