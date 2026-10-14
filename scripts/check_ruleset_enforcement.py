#!/usr/bin/env python3
"""Report whether GitHub branch rules actually enforce the signed-commit gate.

The signed-commit CI workflow (``.github/workflows/signed-commits.yml``) exposes
a status check whose context is the job id ``signed-commits``.  A workflow alone
is advisory: it does not block a merge or a direct push unless the repository
requires that status check through a branch ruleset (or legacy branch
protection) that is actually ``active`` and applies to the default branch.

This operator tool reads the repository's rulesets from the public GitHub REST
API and reports:

* whether an ``active`` ruleset applies to the default branch and requires the
  ``signed-commits`` status check context (enforcement),
* whether such a ruleset exists but is ``disabled``/``evaluate`` (dry run),
* whether a native ``required_signatures`` rule is active (a warning: GitHub's
  native verification reports valid agent commits as unverified).

It is deliberately NOT part of CI and makes no network request unless run
without ``--selftest``.  Exit status: 0 = enforced, 1 = not enforced,
2 = could not determine.
"""

from __future__ import annotations

import argparse
import json
import sys
import urllib.error
import urllib.request

DEFAULT_OWNER = "ottojung"
DEFAULT_REPO = "assemblyp1"
DEFAULT_BRANCH = "main"
DEFAULT_CHECK = "signed-commits"

ACTIVE_ENFORCEMENTS = {"active"}


def _ref_name_applies(conditions: dict, branch: str) -> bool:
    ref_name = (conditions or {}).get("ref_name") or {}
    include = ref_name.get("include") or []
    exclude = ref_name.get("exclude") or []
    applies = any(
        pattern in ("~DEFAULT_BRANCH", "~ALL", branch)
        for pattern in include
    )
    blocked = any(
        pattern in ("~DEFAULT_BRANCH", "~ALL", branch)
        for pattern in exclude
    )
    return applies and not blocked


def _required_status_contexts(rules: list) -> set[str]:
    contexts: set[str] = set()
    for rule in rules or []:
        if rule.get("type") != "required_status_checks":
            continue
        params = rule.get("parameters") or {}
        for check in params.get("required_status_checks") or []:
            context = check.get("context")
            if context:
                contexts.add(context)
    return contexts


def _has_required_signatures(rules: list) -> bool:
    return any((rule or {}).get("type") == "required_signatures" for rule in rules or [])


def evaluate(rulesets: list[dict], branch: str, check: str) -> dict:
    """Evaluate synthetic or live ruleset details.

    ``rulesets`` is a list of ruleset detail objects (the shape returned by
    ``GET /repos/{owner}/{repo}/rulesets/{id}``).
    """
    result = {
        "enforced": False,
        "dry_run": False,
        "native_required_signatures": False,
        "notes": [],
    }
    for rs in rulesets:
        name = rs.get("name") or f"id={rs.get('id')}"
        if rs.get("target") != "branch":
            continue
        if not _ref_name_applies(rs.get("conditions") or {}, branch):
            continue
        rules = rs.get("rules") or []
        enforcement = rs.get("enforcement")
        if enforcement not in ACTIVE_ENFORCEMENTS:
            result["notes"].append(
                f"ruleset {name!r} (id={rs.get('id')}) applies to {branch!r} but "
                f"enforcement={enforcement!r}")
        if _has_required_signatures(rules):
            result["native_required_signatures"] = True
            result["notes"].append(
                f"ruleset {name!r} includes native required_signatures; GitHub "
                "native verification reports valid agent commits as unverified "
                "(bad_email/no_user)")
        contexts = _required_status_contexts(rules)
        if check not in contexts:
            continue
        if enforcement in ACTIVE_ENFORCEMENTS:
            result["enforced"] = True
            result["notes"].append(
                f"ruleset {name!r} is active and requires status check {check!r}")
        elif enforcement == "evaluate":
            result["dry_run"] = True
            result["notes"].append(
                f"ruleset {name!r} requires {check!r} but is in evaluate "
                "(dry-run) mode; it does not block")
        else:
            result["notes"].append(
                f"ruleset {name!r} requires {check!r} but enforcement="
                f"{enforcement!r}; it does not block")
    return result


def _selftest() -> int:
    cases = [
        (
            "active ruleset requiring the check",
            [{"name": "r", "target": "branch", "enforcement": "active",
              "conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}},
              "rules": [{"type": "required_status_checks",
                         "parameters": {"required_status_checks": [{"context": "signed-commits"}]}}]}],
            True,
        ),
        (
            "disabled ruleset requiring the check",
            [{"name": "r", "target": "branch", "enforcement": "disabled",
              "conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}},
              "rules": [{"type": "required_status_checks",
                         "parameters": {"required_status_checks": [{"context": "signed-commits"}]}}]}],
            False,
        ),
        (
            "evaluate (dry-run) ruleset requiring the check",
            [{"name": "r", "target": "branch", "enforcement": "evaluate",
              "conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}},
              "rules": [{"type": "required_status_checks",
                         "parameters": {"required_status_checks": [{"context": "signed-commits"}]}}]}],
            False,
        ),
        (
            "active ruleset requiring a different check",
            [{"name": "r", "target": "branch", "enforcement": "active",
              "conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}},
              "rules": [{"type": "required_status_checks",
                         "parameters": {"required_status_checks": [{"context": "build"}]}}]}],
            False,
        ),
        (
            "active tag ruleset requiring the check",
            [{"name": "r", "target": "tag", "enforcement": "active",
              "conditions": {"ref_name": {"include": ["~ALL"], "exclude": []}},
              "rules": [{"type": "required_status_checks",
                         "parameters": {"required_status_checks": [{"context": "signed-commits"}]}}]}],
            False,
        ),
        (
            "active ruleset excluding the branch",
            [{"name": "r", "target": "branch", "enforcement": "active",
              "conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": ["main"]}},
              "rules": [{"type": "required_status_checks",
                         "parameters": {"required_status_checks": [{"context": "signed-commits"}]}}]}],
            False,
        ),
    ]
    failures = 0
    for desc, fixtures, want in cases:
        got = evaluate(fixtures, DEFAULT_BRANCH, DEFAULT_CHECK)["enforced"]
        status = "PASS" if got == want else "FAIL"
        if got != want:
            failures += 1
        print(f"{status}: {desc} (enforced={got}, want={want})")
    native = evaluate(
        [{"name": "r", "target": "branch", "enforcement": "active",
          "conditions": {"ref_name": {"include": ["~DEFAULT_BRANCH"], "exclude": []}},
          "rules": [{"type": "required_signatures"}]}],
        DEFAULT_BRANCH, DEFAULT_CHECK)
    if native["native_required_signatures"] and not native["enforced"]:
        print("PASS: native required_signatures detected and not counted as enforcement")
    else:
        print("FAIL: native required_signatures detection")
        failures += 1
    print(f"selftest: {len(cases) + 1 - failures} passed, {failures} failed")
    return 0 if failures == 0 else 1


def _api_get(url: str) -> object:
    req = urllib.request.Request(
        url,
        headers={
            "Accept": "application/vnd.github+json",
            "User-Agent": "assemblyp1-ruleset-enforcement-check",
        },
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.load(resp)


def fetch_ruleset_details(owner: str, repo: str) -> list[dict]:
    listing = _api_get(f"https://api.github.com/repos/{owner}/{repo}/rulesets")
    details = []
    for item in listing or []:
        details.append(
            _api_get(f"https://api.github.com/repos/{owner}/{repo}/rulesets/{item['id']}"))
    return details


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--owner", default=DEFAULT_OWNER)
    ap.add_argument("--repo", default=DEFAULT_REPO)
    ap.add_argument("--branch", default=DEFAULT_BRANCH)
    ap.add_argument("--check", default=DEFAULT_CHECK,
                    help="required status check context to look for")
    ap.add_argument("--selftest", action="store_true",
                    help="run offline fixture checks; no network")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        return _selftest()

    try:
        details = fetch_ruleset_details(args.owner, args.repo)
    except urllib.error.HTTPError as exc:
        print(f"error: GitHub API returned HTTP {exc.code} for "
              f"{args.owner}/{args.repo}: {exc.reason}", file=sys.stderr)
        return 2
    except Exception as exc:  # noqa: BLE001 - report any fetch failure
        print(f"error: cannot read rulesets: {exc}", file=sys.stderr)
        return 2

    result = evaluate(details, args.branch, args.check)
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        for note in result["notes"]:
            print(f"note: {note}")
        if result["enforced"]:
            print(f"ENFORCED: {args.branch} requires status check {args.check!r}")
        else:
            print(f"NOT ENFORCED: {args.branch} does not require status check "
                  f"{args.check!r}; the signed-commit gate is advisory only")
    return 0 if result["enforced"] else 1


if __name__ == "__main__":
    sys.exit(main())
