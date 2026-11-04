#!/usr/bin/env python3
"""Summarize llvm-cov JSON for the library code that Lean generated as C.

Compiler-generated helpers (boxed wrappers, derived instances, constructor
eliminators, constant initializers) are excluded: they are not written by hand
and tests cannot target them. Everything else in the library is measured.
"""
import argparse
import collections
import json
import re
import sys

LIBRARY_FILE = re.compile(r"/\.lake/build/ir/Urllib(/|\.c)")
TEST_FILE = re.compile(r"/\.lake/build/ir/UrllibTest")
GENERATED = re.compile(
    r"(___boxed$|_ctorIdx|_ctorElim|_elim(___|$)|_inst[A-Z]|_ofNat$|_init_|initialize_|_closed_|_splitter)"
)
MEMORY_REUSE = re.compile(r"reuseFailAlloc|resetjp|reusejp|isShared|lean_free_object|lean_is_exclusive")
CODE_REGION = 0
_sources = {}


def source_lines(filename):
    if filename not in _sources:
        with open(filename, encoding="utf-8") as handle:
            _sources[filename] = handle.read().split("\n")
    return _sources[filename]


def region_text(filename, region):
    lines = source_lines(filename)
    return "\n".join(lines[region[0] - 1:region[2]])


def branch_text(filename, branch):
    return source_lines(filename)[branch[0] - 1]


def short_file(name):
    return name.split("/.lake/build/ir/", 1)[-1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("export_json")
    parser.add_argument("--fail-under", type=float, default=0.0)
    parser.add_argument("--list-missed", action="store_true")
    parser.add_argument("--show-uncovered", action="store_true")
    args = parser.parse_args()

    with open(args.export_json, encoding="utf-8") as handle:
        functions = json.load(handle)["data"][0]["functions"]

    names = {function["name"] for function in functions}
    stats = collections.defaultdict(lambda: collections.Counter())
    missed = []
    for function in functions:
        if function["name"] + "___redArg" in names:
            continue
        filename = function["filenames"][0]
        if not LIBRARY_FILE.search(filename) or TEST_FILE.search(filename):
            continue
        if GENERATED.search(function["name"]):
            continue
        counter = stats[short_file(filename)]
        counter["functions"] += 1
        counter["functions_hit"] += 1 if function["count"] > 0 else 0
        uncovered_regions = []
        uncovered_arms = 0
        for region in function["regions"]:
            if region[7] != CODE_REGION:
                continue
            if region[4] == 0 and MEMORY_REUSE.search(region_text(filename, region)):
                counter["memory_regions_excluded"] += 1
                continue
            counter["regions"] += 1
            if region[4] > 0:
                counter["regions_hit"] += 1
            else:
                uncovered_regions.append(region)
        for branch in function["branches"]:
            if MEMORY_REUSE.search(branch_text(filename, branch)):
                counter["memory_arms_excluded"] += 2
                continue
            counter["branch_arms"] += 2
            counter["branch_arms_hit"] += (1 if branch[4] > 0 else 0) + (1 if branch[5] > 0 else 0)
            uncovered_arms += (1 if branch[4] == 0 else 0) + (1 if branch[5] == 0 else 0)
        if args.show_uncovered:
            for region in uncovered_regions:
                text = region_text(filename, region).strip().split("\n")[0][:100]
                print(f"  uncovered: {short_file(filename)}:{region[0]} {function['name']}: {text}")
        if function["count"] == 0 or uncovered_regions or uncovered_arms:
            missed.append((short_file(filename), function["name"], function["count"],
                           len(uncovered_regions), uncovered_arms))

    def percent(hit, total):
        return 100.0 * hit / total if total else 100.0

    header = f"{'file':<34}{'functions':>14}{'regions':>16}{'branch arms':>16}"
    print(header)
    print("-" * len(header))
    total = collections.Counter()
    for filename in sorted(stats):
        c = stats[filename]
        total.update(c)
        print(f"{filename:<34}"
              f"{c['functions_hit']:>5}/{c['functions']:<4}{percent(c['functions_hit'], c['functions']):>5.1f}%"
              f"{c['regions_hit']:>6}/{c['regions']:<5}{percent(c['regions_hit'], c['regions']):>5.1f}%"
              f"{c['branch_arms_hit']:>6}/{c['branch_arms']:<5}{percent(c['branch_arms_hit'], c['branch_arms']):>5.1f}%")
    print("-" * len(header))
    region_percent = percent(total["regions_hit"], total["regions"])
    branch_percent = percent(total["branch_arms_hit"], total["branch_arms"])
    print(f"{'TOTAL':<34}"
          f"{total['functions_hit']:>5}/{total['functions']:<4}{percent(total['functions_hit'], total['functions']):>5.1f}%"
          f"{total['regions_hit']:>6}/{total['regions']:<5}{region_percent:>5.1f}%"
          f"{total['branch_arms_hit']:>6}/{total['branch_arms']:<5}{branch_percent:>5.1f}%")

    print(f"excluded as runtime memory reuse: {total['memory_regions_excluded']} uncovered regions, "
          f"{total['memory_arms_excluded']} branch arms")

    if args.list_missed:
        print()
        print("functions with uncovered code (name, calls, uncovered regions, uncovered branch arms):")
        for filename, name, count, regions, arms in sorted(missed):
            print(f"  {filename}: {name}  calls={count} regions={regions} arms={arms}")

    if min(region_percent, branch_percent) < args.fail_under:
        print(f"coverage below {args.fail_under}%", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
