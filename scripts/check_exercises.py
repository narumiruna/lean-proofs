"""Validate the Rudin inventory and prepare the Lean environment audit."""

import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COUNTS = (20, 30, 25, 26, 29, 19, 26, 31, 31, 32, 18)
STATUSES = {"todo", "in_progress", "blocked", "verified"}
KINDS = {"proof", "counterexample", "construction", "classification"}
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z")
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.]+)\s*$", re.M)


class InventoryError(ValueError):
    """The inventory or delivered source structure is invalid."""


def require(condition, message):
    if not condition:
        raise InventoryError(message)


def module_path(root, module):
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def local_imports(root, module, seen=None):
    seen = set() if seen is None else seen
    if module in seen:
        return seen
    path = module_path(root, module)
    if not path.is_file():
        return seen
    seen.add(module)
    for imported in IMPORT.findall(path.read_text()):
        if imported == "Math" or imported.startswith("Math."):
            local_imports(root, imported, seen)
    return seen


def proof_fingerprint(root, module):
    return {name: hashlib.sha256(module_path(root, name).read_bytes()).hexdigest()
            for name in sorted(local_imports(root, module))}


def environment_fingerprint(root):
    digest = hashlib.sha256()
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        path = root / name
        require(path.is_file(), f"Missing pinned environment file: {name}")
        digest.update(name.encode() + b"\0" + path.read_bytes() + b"\0")
    return digest.hexdigest()


def validate(data, root=ROOT, final=False):
    require(data.get("schema_version") == 1, "Unsupported inventory schema")
    chapters = data.get("chapters", [])
    require([c.get("number") for c in chapters] == list(range(1, 12)), "Expected chapters 1–11")
    require(tuple(c.get("exercise_count") for c in chapters) == COUNTS, "Chapter counts differ from source")
    exercises = data.get("exercises", [])
    require(len(exercises) == sum(COUNTS), "Missing or extra exercise")
    source = data.get("source", {})
    require(source.get("exercise_count") == sum(COUNTS), "Source exercise count mismatch")
    require(re.fullmatch(r"[a-f0-9]{64}", source.get("sha256", "")), "Missing source hash")
    require(bool(source.get("title")) and bool(source.get("edition")), "Missing source identity")
    ids, obligation_ids, declarations = set(), set(), set()
    modules, targets = set(), []
    status_counts, chapter_stats = Counter(), {}
    for chapter in chapters:
        chapter_stats[chapter["number"]] = {"exercises": 0, "verified": 0, "as_stated": 0,
                                            "corrected": 0, "obligations": 0, "verified_obligations": 0}
    for exercise in exercises:
        chapter, number = exercise.get("chapter"), exercise.get("number")
        require(isinstance(chapter, int) and 1 <= chapter <= 11, "Invalid chapter")
        require(isinstance(number, int) and 1 <= number <= COUNTS[chapter - 1], "Invalid exercise number")
        expected_id = f"R{chapter:02}E{number:02}"
        require(exercise.get("id") == expected_id and expected_id not in ids, f"Duplicate or invalid ID: {expected_id}")
        ids.add(expected_id)
        expected_module = f"Math.Rudin.Chapter{chapter:02}.Exercise{number:02}"
        require(exercise.get("module") == expected_module, f"Wrong module: {expected_id}")
        modules.add(expected_module)
        require(bool(exercise.get("summary", "").strip()), f"Missing summary: {expected_id}")
        books, pdfs = exercise.get("book_pages", []), exercise.get("pdf_pages", [])
        require(bool(books) and len(books) == len(pdfs), f"Missing source pages: {expected_id}")
        bounds = chapters[chapter - 1]["book_pages"]
        require(books == sorted(set(books)) and all(isinstance(p, int) and bounds[0] <= p <= bounds[1] for p in books), f"Invalid source span: {expected_id}")
        require(pdfs == [p + 9 for p in books], f"PDF/book page mismatch: {expected_id}")
        require(exercise.get("source_review", {}).get("method") in {"ocr", "ocr+image"}, f"Missing source review: {expected_id}")
        require(exercise.get("disposition") in {"as_stated", "needs_review", "refuted_and_corrected"}, f"Missing disposition: {expected_id}")
        obligations = exercise.get("obligations", [])
        require(bool(obligations), f"Missing obligations: {expected_id}")
        require(exercise.get("obligation_count") == len(obligations), f"Missing or extra subquestion: {expected_id}")
        all_verified = True
        for obligation in obligations:
            oid = obligation.get("id", "")
            require(oid.startswith(expected_id + ".") and NAME.fullmatch(oid), f"Invalid obligation ID: {oid}")
            require(oid not in obligation_ids, f"Duplicate obligation: {oid}")
            obligation_ids.add(oid)
            require(bool(obligation.get("summary", "").strip()), f"Missing contract: {oid}")
            require(obligation.get("kind") in KINDS, f"Invalid obligation kind: {oid}")
            status = obligation.get("status")
            require(status in STATUSES, f"Invalid status: {oid}")
            status_counts[status] += 1
            refs = obligation.get("declarations")
            require(isinstance(refs, list), f"Invalid declaration list: {oid}")
            if status == "verified":
                require(bool(refs), f"Verified obligation has no theorem: {oid}")
                evidence = obligation.get("evidence")
                require(isinstance(evidence, dict), f"Missing verification evidence: {oid}")
                review = evidence.get("semantic_review")
                require(isinstance(review, dict) and review.get("result") == "passed"
                        and isinstance(review.get("reviewer"), str) and bool(review["reviewer"].strip())
                        and isinstance(review.get("notes"), str) and bool(review["notes"].strip()),
                        f"Missing successful semantic review evidence: {oid}")
                results = evidence.get("checks")
                require(isinstance(results, dict) and all(results.get(key) == "passed" for key in
                        ("single_file", "project_build", "axiom_audit", "coverage")),
                        f"Missing successful check evidence: {oid}")
                require(evidence.get("source_hashes") == proof_fingerprint(root, expected_module),
                        f"Stale proof-source evidence: {oid}; reopen and review the changed source")
                require(evidence.get("environment_sha256") == environment_fingerprint(root),
                        f"Stale environment evidence: {oid}; revalidate the pinned dependencies")
            else:
                all_verified = False
                require(not final, f"Unfinished obligation: {oid} ({status})")
            for declaration in refs:
                require(isinstance(declaration, str) and NAME.fullmatch(declaration), f"Invalid declaration name: {oid}")
                require(declaration.startswith(f"Rudin.Chapter{chapter:02}."), f"Wrong declaration namespace: {oid}")
                declarations.add(declaration)
                targets.append({"name": declaration, "module": expected_module, "obligation": oid})
        issues = exercise.get("issues", [])
        require(isinstance(issues, list), f"Invalid issues: {expected_id}")
        for issue in issues:
            require(bool(issue.get("summary")) and issue.get("resolution") in {"pending", "resolved"}, f"Invalid source issue: {expected_id}")
            if issue["resolution"] == "resolved":
                require(bool(issue.get("evidence")), f"Missing issue resolution evidence: {expected_id}")
        if all_verified:
            require(all(i["resolution"] == "resolved" for i in issues), f"Unresolved source issue: {expected_id}")
            require(exercise["disposition"] != "needs_review", f"Unresolved disposition: {expected_id}")
        if targets and any(t["module"] == expected_module for t in targets):
            require(module_path(root, expected_module).is_file(), f"Missing delivery file: {expected_id}")
        stats = chapter_stats[chapter]
        stats["exercises"] += 1
        stats["verified"] += all_verified
        stats["as_stated"] += all_verified and exercise["disposition"] == "as_stated"
        stats["corrected"] += all_verified and exercise["disposition"] == "refuted_and_corrected"
        stats["obligations"] += len(obligations)
        stats["verified_obligations"] += sum(o["status"] == "verified" for o in obligations)
    require(source.get("obligation_count") == len(obligation_ids), "Total subquestion count mismatch")
    for exercise in exercises:
        require(all(dep in ids or dep in obligation_ids for dep in exercise.get("depends_on", [])), f"Unknown dependency: {exercise['id']}")
    reachable = local_imports(root, "Math")
    delivered = {"Math.Rudin"}
    for path in (root / "Math" / "Rudin").rglob("*.lean"):
        module = ".".join(path.relative_to(root).with_suffix("").parts)
        require(module in modules or module.startswith("Math.Rudin.Support."), f"Unlisted exercise module: {module}")
        delivered.add(module)
    require(delivered <= reachable, f"Delivery not imported from Math: {sorted(delivered - reachable)}")
    return {"modules": sorted(delivered), "targets": targets}, chapter_stats, status_counts


def progress_text(data, stats, statuses):
    lines = ["# Rudin progress", "", "Generated from `exercises.json`. Do not edit counts by hand.", "", "| Chapter | Verified resolutions | As stated | Refuted/corrected | Verified obligations |", "| --- | --- | --- | --- | --- |"]
    for chapter, row in stats.items():
        lines.append(f"| {chapter} | {row['verified']}/{row['exercises']} | {row['as_stated']} | {row['corrected']} | {row['verified_obligations']}/{row['obligations']} |")
    verified = sum(row["verified"] for row in stats.values())
    as_stated = sum(row["as_stated"] for row in stats.values())
    corrected = sum(row["corrected"] for row in stats.values())
    lines.extend(["", f"Total: **{verified}/{len(data['exercises'])} verified resolutions**; **{statuses['verified']}/{sum(statuses.values())} obligations** verified.", "", f"These comprise {as_stated} exercises proved as stated and {corrected} false source claims resolved by counterexamples and explicit corrections. A refuted claim is not counted as a proved original statement.", "", "## Source issues and blockers", ""])
    for exercise in data["exercises"]:
        for issue in exercise["issues"]:
            if issue["resolution"] == "pending":
                lines.append(f"- `{exercise['id']}`: {issue['summary']}")
        for obligation in exercise["obligations"]:
            if obligation["status"] == "blocked":
                lines.append(f"- `{obligation['id']}`: blocked; {obligation.get('blocker', 'see obligation evidence')}")
    lines.extend(["", "## Validation limits", "", "Source inventory is not proof completion. A verified count requires source-to-type review, compilation, and the axiom audit. Full-plan completion and clean-checkout validation have not been established by this table.", "", "See `mathlib-coverage.md` for representation gaps and `errata.md` for source corrections.", ""])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--final", action="store_true", help="Reject every unfinished obligation")
    parser.add_argument("--update-progress", action="store_true", help="Regenerate the retained progress table")
    args = parser.parse_args()
    try:
        data = json.loads((ROOT / "exercises.json").read_text())
        request, stats, statuses = validate(data, final=args.final)
        progress = progress_text(data, stats, statuses)
        path = ROOT / "docs/rudin/progress.md"
        if args.update_progress:
            path.write_text(progress)
        else:
            require(path.is_file() and path.read_text() == progress, "Progress is stale; run with --update-progress")
        out = ROOT / ".lake/rudin-check/request.json"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(request, indent=2) + "\n")
        print(f"Inventory passed: {len(data['exercises'])} exercises, {sum(statuses.values())} obligations, {statuses['verified']} verified obligations.")
    except (InventoryError, ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(1, f"Inventory check failed: {error}\n")


if __name__ == "__main__":
    main()
