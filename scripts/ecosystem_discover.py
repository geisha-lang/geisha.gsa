#!/usr/bin/env python3
"""Discover active Geisha ecosystem repositories under geisha-lang for CI matrix generation.

Reads .github/ecosystem.json for exclusions and per-repo overrides, queries the GitHub API
for all non-archived public repositories in the org, and automatically includes any new
repository that contains a root `geisha.toml`.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
CONFIG_PATH = ROOT / ".github" / "ecosystem.json"


def gh_get_json(url: str, token: str | None) -> tuple[int, Any]:
    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "geisha-ecosystem-ci",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(url, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            return resp.status, json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        if exc.code == 404:
            return 404, None
        body = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"GitHub API {url} returned HTTP {exc.code}: {body}") from exc


def list_org_repos(org: str, token: str | None) -> list[dict[str, Any]]:
    repos: list[dict[str, Any]] = []
    page = 1
    while True:
        url = f"https://api.github.com/orgs/{org}/repos?type=public&per_page=100&page={page}"
        _, batch = gh_get_json(url, token)
        if not isinstance(batch, list) or not batch:
            break
        repos.extend(batch)
        if len(batch) < 100:
            break
        page += 1
    return repos


def has_geisha_toml(org: str, repo: str, token: str | None) -> bool:
    status, _ = gh_get_json(
        f"https://api.github.com/repos/{org}/{repo}/contents/geisha.toml",
        token,
    )
    return status == 200


def discover_targets(config: dict[str, Any], token: str | None, filter_repo: str = "") -> list[dict[str, Any]]:
    org = config["org"]
    exclude = set(config.get("exclude", []))
    default_target = config["default_target"]
    overrides: dict[str, Any] = config.get("overrides", {})

    repos = list_org_repos(org, token)
    targets: list[dict[str, Any]] = []

    for repo_info in sorted(repos, key=lambda r: r["name"]):
        name = repo_info["name"]
        if repo_info.get("archived") or repo_info.get("disabled"):
            continue
        if name in exclude:
            continue
        if filter_repo and name != filter_repo:
            continue

        override = overrides.get(name)
        if override is not None:
            if "targets" in override:
                for entry in override["targets"]:
                    targets.append(
                        {
                            "repo": name,
                            "label": entry.get("label", name),
                            "os": entry.get("os", default_target["os"]),
                            "deps": entry.get("deps", default_target["deps"]),
                            "cmd": entry.get("cmd", default_target["cmd"]),
                            "default_branch": repo_info.get("default_branch", "main"),
                        }
                    )
                continue

            if not override.get("include", False) and not has_geisha_toml(org, name, token):
                continue

            targets.append(
                {
                    "repo": name,
                    "label": override.get("label", name),
                    "os": override.get("os", default_target["os"]),
                    "deps": override.get("deps", default_target["deps"]),
                    "cmd": override.get("cmd", default_target["cmd"]),
                    "default_branch": repo_info.get("default_branch", "main"),
                }
            )
            continue

        if has_geisha_toml(org, name, token):
            targets.append(
                {
                    "repo": name,
                    "label": name,
                    "os": default_target["os"],
                    "deps": list(default_target["deps"]),
                    "cmd": default_target["cmd"],
                    "default_branch": repo_info.get("default_branch", "main"),
                }
            )

    return targets


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=CONFIG_PATH)
    parser.add_argument("--repo", default="", help="Optional single repository name to filter")
    parser.add_argument("--github-output", type=Path, default=None, help="Path to $GITHUB_OUTPUT")
    args = parser.parse_args()

    config = json.loads(args.config.read_text(encoding="utf-8"))
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    targets = discover_targets(config, token, filter_repo=args.repo.strip())

    if args.repo.strip() and not targets:
        print(f"No ecosystem target matched filter repo={args.repo!r}", file=sys.stderr)
        return 1

    linux_targets = [t for t in targets if t["os"].startswith("ubuntu")]
    macos_targets = [t for t in targets if t["os"].startswith("macos")]

    print(
        f"Discovered {len(targets)} ecosystem targets "
        f"({len(linux_targets)} Linux, {len(macos_targets)} macOS):"
    )
    for t in targets:
        deps_str = ",".join(t["deps"]) if t["deps"] else "none"
        print(f"  - {t['label']} [{t['os']}] (repo={t['repo']}, deps={deps_str})")

    if args.github_output:
        with args.github_output.open("a", encoding="utf-8") as fh:
            fh.write(f"linux_matrix={json.dumps(linux_targets, separators=(',', ':'))}\n")
            fh.write(f"macos_matrix={json.dumps(macos_targets, separators=(',', ':'))}\n")
            fh.write(f"has_linux={'true' if linux_targets else 'false'}\n")
            fh.write(f"has_macos={'true' if macos_targets else 'false'}\n")
            fh.write(f"total={len(targets)}\n")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
