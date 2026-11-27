"""Recount physical source lines for named Weil II proof routes (Python 3.10+)."""
import argparse
import base64
import csv
import hashlib
import io
import json
import lzma
import multiprocessing
import os
from collections import Counter, defaultdict
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


PACKAGES = ("WeilII", "WeilConjectures")
RANGES = ("old_only_ranges", "new_only_ranges", "shared_ranges")
COVERAGE = ("old_decls", "new_decls", "shared_decls", "old_unmapped", "new_unmapped")
LINES = ("old_only_lines", "new_project_only_lines", "new_upstream_only_lines", "shared_lines")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def git(checkout, *args):
    # The explicit directory also works in a read-only checkout owned by another user.
    return subprocess.check_output(["git", "-c", f"safe.directory={checkout}", "-C",
                                    str(checkout), *args], text=True).strip()


def load_inputs(root, docs, upstream):
    spec = json.loads((docs / "route-roots.json").read_bytes())
    index = json.loads((root / "traces/index.json").read_bytes())
    manifest = json.loads((root / "lake-manifest.json").read_bytes())
    pins = {p["name"].strip("«»"): p["rev"] for p in manifest["packages"]}
    require(pins["weil-conjectures"] == spec["upstreamRevision"] == index["upstreamRevision"],
            "upstream revision differs")
    require(pins["mathlib"] == spec["mathlibRevision"], "Mathlib revision differs")
    require((root / "lean-toolchain").read_text().strip() == spec["toolchain"], "toolchain differs")
    for key, target in spec["targets"].items():
        ((module, name),) = spec["roots"][key]["seeds"]
        require(name in index["modules"][module]["roots"], f"absent from module roots: {name}")
        if "targets" in index or index.get("status") != "candidate":
            entry = index["targets"][target["indexKey"]]
            require((module, name) == (entry["module"], entry["declaration"]),
                    f"target declaration differs for {key}")
    require(git(upstream, "rev-parse", "HEAD") == pins["weil-conjectures"], "wrong upstream HEAD")
    return spec


def source_info(module, root, upstream):
    package, *names = module.split(".")
    require(package in PACKAGES and all(n.isidentifier() for n in names), f"invalid module {module}")
    rel = Path(package, *names).with_suffix(".lean")
    path = (root if package == "WeilII" else upstream) / rel
    data = path.read_bytes()
    return (data.count(b"\n") + int(bool(data) and not data.endswith(b"\n")), sha(data))


def spans(numbers):
    result = []
    for n in numbers:
        if result and result[-1][1] + 1 == n:
            result[-1][1] = n
        else:
            result.append([n, n])
    return ",".join(str(a) if a == b else f"{a}-{b}" for a, b in result)


def parse_spans(cell, limit):
    result = set()
    last = 0
    for run in cell.split(",") if cell else []:
        first, sep, end = run.partition("-")
        a, b = int(first), int(end) if sep else int(first)
        require(last < a <= b <= limit, f"overlapping or out-of-source range {run}")
        result.update(range(a, b + 1))
        last = b
    return result


def public_ranges(spec):
    """Open the losslessly compressed, tab-separated rows accompanying the seeds."""
    data = spec["frozenInventory"]
    require(data["encoding"] == "xz+base64", "unsupported inventory encoding")
    packed = base64.b64decode(data["data"], validate=True)
    require(sha(packed) == data["xzSha256"], "frozen inventory checksum differs")
    return lzma.open(io.BytesIO(packed), mode="rt", encoding="utf-8", newline="")


def frozen_rows(inventory, scopes, root, upstream):
    csv.field_size_limit(1 << 30)
    cache = {}
    source_index = {}
    table = inventory.open(encoding="utf-8", newline="") if isinstance(inventory, Path) else inventory
    with table:
        reader = csv.DictReader(table, delimiter="\t")
        fields = set(reader.fieldnames or [])
        needed = {"package", "module", "source_sha256", "file_lines", "footprint",
                  *RANGES, *LINES, *COVERAGE}
        require(needed <= fields and {"scope", "scopes"} & fields, "inventory lacks the public range columns")
        for row in reader:
            module = row["module"]
            labels = row["scopes"].split(",") if "scopes" in fields else [row["scope"]]
            if labels == ["module-index"]:
                source_index[module] = row["source_sha256"]
                continue
            selected = [s for s in labels if s in scopes]
            if not selected:
                continue
            package = row["package"]
            require(package == module.partition(".")[0], f"package differs for {module}")
            if module not in cache:
                cache[module] = source_info(module, root, upstream)
            length, digest = cache[module]
            expected = row["source_sha256"] or source_index.get(module)
            require((length, digest) == (int(row["file_lines"]), expected),
                    f"source bytes differ for {module}")
            old, new, both = [parse_spans(row[k], length) for k in RANGES]
            require(not (old & new or old & both or new & both), f"overlap in {module}")
            counts = [len(old), len(new) if package == "WeilII" else 0,
                      len(new) if package == "WeilConjectures" else 0, len(both)]
            require(counts == [int(row[k]) for k in LINES], f"range totals differ in {module}")
            coverage = [int(row[k]) for k in COVERAGE]
            ranges = [spans(sorted(group)) for group in (old, new, both)]
            for s in selected:
                yield s, module, length, digest, coverage, counts, ranges, row["footprint"]


def collect_closures(spec, docs, work, bits, batch_size):
    libs = [Path(p).resolve() for p in os.environ.get("LEAN_PATH", "").split(os.pathsep) if p]
    mathlib = next((p for lib in libs if (lib / "Mathlib").is_dir() for p in lib.parents
                    if (p / "Mathlib.lean").is_file() and (p / ".git").exists()), None)
    require(mathlib is not None and git(mathlib, "rev-parse", "HEAD") == spec["mathlibRevision"],
            "run under lake env with the pinned Mathlib checkout built")
    version = subprocess.check_output(["lean", "--version"], text=True)
    expected = spec["toolchain"].split(":v")[-1]
    require(re.search(r"\bversion " + re.escape(expected) + r"\b", version), "unexpected Lean version")
    helper, plan = work / "RouteQuery.lean", work / "plan.tsv"
    shutil.copyfile(docs / "route-range-query.txt", helper)
    jobs = {}
    for key in bits:
        data = spec["roots"][key]
        seedfile, imports, trace = (work / f"{key}.{ext}" for ext in ("tsv", "imports", "jsonl"))
        seedfile.write_text("".join(f"{m}\t{n}\n" for m, n in data["seeds"]), encoding="utf-8")
        imports.write_text("\n".join(data["imports"]) + "\n", encoding="utf-8")
        jobs[key] = "\t".join(map(str, (seedfile, imports, trace)))
    cmd = ["lean", "--run", str(helper)]
    ambiguity = {}
    def replay(keys):
        plan.write_text("\n".join(jobs[k] for k in keys) + "\n", encoding="utf-8")
        index = work / (keys[0] + "-ambiguous.jsonl")
        batch = subprocess.run([*cmd, "walk", str(plan), str(index)])
        if batch.returncode and len(keys) > 1:
            middle = len(keys) // 2
            replay(keys[:middle])
            replay(keys[middle:])
        else:
            batch.check_returncode()
            if len(keys) > 1:
                ambiguity.update(dict.fromkeys(keys, index))

    keys = list(jobs)
    size = batch_size or len(keys)
    for i in range(0, len(keys), size):
        replay(keys[i:i + size])
    owners = defaultdict(dict)
    sizes = {}
    for k, bit in bits.items():
        trace = work / f"{k}.jsonl"
        expected = spec["roots"][k]["traceSha256"]
        # Joint imports can change resolution of a generated declaration. Accept a
        # joint result only if every (owner, declaration) row matches the original.
        if file_sha(trace) != expected:
            if k in ambiguity:
                local = work / "local-owners.jsonl"
                subprocess.run([*cmd, "owners", str(work / f"{k}.imports"), str(work / f"{k}.tsv"),
                                str(ambiguity[k]), str(local)], check=True)
                with local.open("rb") as rows:
                    corrections = {json.loads(line)[1]: line for line in rows}
                corrected = work / "corrected.jsonl"
                with trace.open("rb") as rows, corrected.open("wb") as output:
                    for line in rows:
                        output.write(corrections.get(json.loads(line)[1], line))
                corrected.replace(trace)
            if file_sha(trace) != expected:
                replay([k])
            require(file_sha(trace) == expected, f"{k} exact closure digest differs")
        actual = 0
        with trace.open(encoding="utf-8") as rows:
            for line in rows:
                owner, name = json.loads(line)
                actual += 1
                if owner and owner.partition(".")[0] in PACKAGES:
                    previous = owners[owner].get(name, 0)
                    require(not previous & bit, f"duplicate declaration {owner} / {name}")
                    owners[owner][name] = previous | bit
        sizes[k] = actual
        trace.unlink()
    return owners, sizes


def mapped_rows(owners, bits, scopes, root, upstream):
    libs = [Path(p).resolve() for p in os.environ.get("LEAN_PATH", "").split(os.pathsep) if p]
    require(libs, "use lake env python3 docs/recount.py --closures")
    selections = {s: (sum(bits[k] for k in data["old"]), sum(bits[k] for k in data["new"]))
                  for s, data in scopes.items()}
    for module, names in owners.items():
        length, digest = source_info(module, root, upstream)
        rel = Path(*module.split(".")).with_suffix(".olean")
        olean = next((lib / rel for lib in libs if (lib / rel).is_file()), None)
        require(olean is not None, f"missing compiled module {module}")
        ilean = olean.with_suffix(".ilean")
        locations = {}
        if ilean.is_file():
            idx = json.loads(ilean.read_bytes())
            require(idx.get("module", module) == module, f"wrong declaration index for {module}")
            locations = idx["decls"]
        line_masks = [0] * length
        flags, missing = Counter(names.values()), Counter()
        for name, mask in names.items():
            if name not in locations:
                missing[mask] += 1
                continue
            a, col, b, end = locations[name][:4]
            stop = b + (end > 0)
            if not (0 <= a <= stop <= length and (a, col) < (b, end)):
                missing[mask] += 1
                continue
            for i in range(a, stop):
                line_masks[i] |= mask
        for s, (old, new) in selections.items():
            def count(freq, left):
                return sum(n for mask, n in freq.items() if mask & left)
            a, b = count(flags, old), count(flags, new)
            if not (a or b):
                continue
            shared = sum(n for mask, n in flags.items() if mask & old and mask & new)
            coverage = [a, b, shared, count(missing, old), count(missing, new)]
            groups = [[], [], [], []]
            for i, mask in enumerate(line_masks, 1):
                side = int(bool(mask & old)) + 2 * int(bool(mask & new))
                if side:
                    groups[side].append(i)
            _, only_old, only_new, common = groups
            project = module.partition(".")[0] == "WeilII"
            counts = [len(only_old), len(only_new) if project else 0,
                      0 if project else len(only_new), len(common)]
            yield (s, module, length, digest, coverage, counts,
                   [spans(group) for group in groups[1:]],
                   "shared" if a and b else "old-only" if a else "new-only")


def write_module_rows(output, shard, bits, scopes, root, upstream):
    with output.open("w", encoding="utf-8") as rows:
        for row in mapped_rows(shard, bits, scopes, root, upstream):
            rows.write(json.dumps(row, ensure_ascii=False, separators=(",", ":")) + "\n")


def partition_modules(owners, bits, scopes, root, upstream, work, jobs):
    count = min(jobs, len(owners))
    if count <= 1:
        yield from mapped_rows(owners, bits, scopes, root, upstream)
        return
    modules = sorted(owners)
    outputs = [work / f"module-rows-{i}.jsonl" for i in range(count)]
    context = multiprocessing.get_context("fork" if "fork" in multiprocessing.get_all_start_methods() else "spawn")
    children = []
    for i, output in enumerate(outputs):
        shard = {m: owners[m] for m in modules[i::count]}
        child = context.Process(target=write_module_rows,
                                args=(output, shard, bits, scopes, root, upstream))
        child.start()
        children.append(child)
    for child in children:
        child.join()
    require(all(child.exitcode == 0 for child in children), "a module range worker failed")
    print(f"Mapped {len(modules)} modules in {count} source-range processes.", file=sys.stderr)
    for output in outputs:
        with output.open(encoding="utf-8") as rows:
            for line in rows:
                yield json.loads(line)


def summarize(rows, scopes):
    summaries = {s: Counter() for s in scopes}
    fingerprints = {s: {} for s in scopes}
    for s, module, length, digest, coverage, counts, ranges, footprint in rows:
        require(module not in fingerprints[s], f"duplicate module {module} in {s}")
        a, b, shared, om, nm = coverage
        require(a + b > 0 and 0 <= shared <= min(a, b) and 0 <= om <= a and 0 <= nm <= b,
                f"inconsistent declaration counts in {s} / {module}")
        require(footprint == ("shared" if a and b else "old-only" if a else "new-only"),
                f"inconsistent module footprint in {s} / {module}")
        totals = summaries[s]
        totals.update(dict(zip(COVERAGE, coverage)))
        totals.update(dict(zip(LINES, counts)))
        group = footprint + "_" + module.partition(".")[0]
        totals["modules_" + group] += 1
        totals["file_" + group] += length
        fingerprints[s][module] = [length, digest, coverage, ranges]
    result = {}
    for s, totals in summaries.items():
        require(fingerprints[s], f"missing scope {s}")
        data = json.dumps(sorted(fingerprints[s].items()), ensure_ascii=False,
                          separators=(",", ":")).encode("utf-8")
        d = dict(totals, moduleRangeSha256=sha(data))
        o, p, u, c = (totals[k] for k in LINES)
        matched = scopes[s]["alignment"] == "same-conclusion"
        d.update(old_total=o+c if scopes[s]["old"] else None,
                 new_total=p+u+c if scopes[s]["new"] else None,
                 net=o-p-u if matched else None, denominator=o+c if matched else None)
        result[s] = d
    return result


def bridge_counts(results, scopes, roots):
    for scope, row in results.items():
        if scopes[scope]["alignment"] != "same-conclusion":
            continue
        for side in ("old", "new"):
            (key,) = scopes[scope][side]
            # Each bridge theorem in the supplied sources is one blank-line-delimited block.
            blocks = [b for b in roots[key]["witnessLean"].split("\n\n")
                      if b.startswith(("theorem ", "private theorem "))]
            require(blocks and all(":= by\n" in b for b in blocks), f"malformed bridge {key}")
            row[side + "_bridge_lines"] = sum(len(b.splitlines()) for b in blocks)
            row[side + "_bridge_body_lines"] = sum(len(b.split(":= by\n", 1)[1].splitlines()) for b in blocks)
        row["net_with_bridges"] = row["net"] + row["old_bridge_lines"] - row["new_bridge_lines"]
        row["denominator_with_bridge"] = row["denominator"] + row["old_bridge_lines"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent,
                        help="public project root (default: parent of docs)")
    parser.add_argument("--upstream", type=Path, help="pinned weil-conjectures checkout")
    parser.add_argument("--inventory", type=Path, help="read the source ranges from this complete TSV")
    parser.add_argument("--export-inventory", type=Path, help="write the embedded source ranges as a readable TSV")
    parser.add_argument("--scope", action="append", help="select a comparison; repeatable")
    parser.add_argument("--closures", action="store_true", help="derive fresh kernel closures and .ilean ranges")
    parser.add_argument("--batch-size", type=int, help="maximum groups per Lean process (default: all selected)")
    parser.add_argument("--jobs", type=int, default=4, help="number of parallel source-range processes")
    parser.add_argument("--output", type=Path, help="save the checked counts, footprints and range digests as JSON")
    args = parser.parse_args()
    require(args.jobs > 0 and (args.batch_size is None or args.batch_size > 0), "choose positive batch and job sizes")
    root = args.root.resolve()
    docs = root / "docs"
    upstream = (args.upstream or root / ".lake/packages/weil-conjectures").resolve()
    spec = load_inputs(root, docs, upstream)
    if args.export_inventory:
        with public_ranges(spec) as source, args.export_inventory.open("w", encoding="utf-8", newline="") as dest:
            shutil.copyfileobj(source, dest)
    scopes = spec["scopes"]
    if args.scope:
        require(set(args.scope) <= scopes.keys(), "unknown scope; see route-roots.json")
        scopes = {s: scopes[s] for s in dict.fromkeys(args.scope)}
    with tempfile.TemporaryDirectory() as work:
        if args.closures:
            keys = sorted({k for s in scopes.values() for k in s["old"] + s["new"]})
            bits = {k: 1 << i for i, k in enumerate(keys)}
            owners, sizes = collect_closures(spec, docs, Path(work), bits, args.batch_size)
            for k, actual in sizes.items():
                require(actual == spec["roots"][k]["reachable"], f"{k} closure has {actual} declarations")
            rows = partition_modules(owners, bits, scopes, root, upstream, Path(work), args.jobs)
        else:
            inventory = args.inventory or docs / "module-inventory.tsv"
            source = inventory if args.inventory or inventory.exists() else public_ranges(spec)
            rows = frozen_rows(source, scopes, root, upstream)
        results = summarize(rows, scopes)
        bridge_counts(results, scopes, spec["roots"])
    for s, row in results.items():
        expected = spec["reference"][s]
        for key in sorted(set(expected) | set(row)):
            require(row.get(key) == expected.get(key), f"{s} / {key}: {row.get(key)} != {expected.get(key)}")
    if args.output:
        args.output.write_text(json.dumps(results, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print("scope\told-only\tnew-WeilII\tnew-PKU\tshared\tnet\told-denominator\tnet/old")
    for s, row in results.items():
        net, denom = row["net"], row["denominator"]
        comparison = ["—"] * 3 if net is None else [f"{net:+d}", str(denom), f"{net/denom:+.2%}"]
        print("\t".join([s, *(str(row[k]) for k in LINES), *comparison]))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
