"""Recompute all registered checkpoints from the portable production ledgers."""
import argparse
from collections import Counter
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import sys
from tempfile import NamedTemporaryFile, TemporaryDirectory
from urllib.request import urlopen
from zipfile import ZipFile

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "src"))
from plan.allcp_bracket import K_JCSA_1, N_K
from jcsa.screen_interval import FULL_N_LOOKS, full_interval, CHEAP_N, LATE_CHEAP_N


TAG = "jcsa-otb-20261122"
ARCHIVE = f"{TAG}-evidence.zip"
RELEASE_URL = f"https://github.com/jh85/chushogicount-paper/releases/download/{TAG}/{ARCHIVE}"
ARCHIVE_SHA256 = "b3dc4b35b67676503e4a9c3c8584f26829b2c9bb7ea750e5d6ee6f5913702b77"


def archive_hash(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def release_archive(directory):
    cached = directory / ARCHIVE
    if cached.exists() and archive_hash(cached) == ARCHIVE_SHA256:
        return cached
    print(f"Downloading {ARCHIVE} to {directory}", file=sys.stderr)
    with NamedTemporaryFile(dir=directory, delete=False) as download:
        pending = Path(download.name)
    try:
        with urlopen(RELEASE_URL, timeout=120) as response, pending.open("wb") as output:
            shutil.copyfileobj(response, output)
        require(archive_hash(pending) == ARCHIVE_SHA256, "downloaded evidence checksum mismatch")
        pending.replace(cached)
    finally:
        pending.unlink(missing_ok=True)
    return cached


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rows(path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt") as stream:
        for line in stream:
            yield json.loads(line)


def read(path):
    return json.loads(path.read_bytes())


def screen_totals(data, config):
    plan = config["precision"]
    domains = [plan["domains"][key] for key in ("cheap_first", "cheap_extra")]
    grouped = {domain: [] for domain in domains}
    for row in rows(data / "screen-blocks.jsonl.gz"):
        grouped[row["domain"]].append(row)
    totals = []
    for domain, size in zip(domains, (CHEAP_N, LATE_CHEAP_N - CHEAP_N), strict=True):
        count = 0
        blocks = grouped[domain]
        starts = list(range(0, size, plan["cheap_block"]))
        require(len(blocks) == len(starts), "wrong screen block count")
        for block, first in zip(blocks, starts, strict=True):
            stop = min(size, first + plan["cheap_block"])
            by_reason = block["indices_by_reason"]
            indices = [i for group in by_reason.values() for i in group]
            require(set(by_reason) <= {"I10", "complete one-ply mate refutation"}, "unknown exclusion")
            require((block["first"], block["stop"]) == (first, stop), "screen block range")
            require(len(indices) == len(set(indices)) == block["excluded"], "screen exclusions")
            require(all(first <= i < stop for i in indices), "screen index outside block")
            count += len(indices)
        totals.append(count)
    return totals


def audit_blocks(data, blocks):
    with gzip.open(data / "first-pass-audits.jsonl.gz", "rb") as stream:
        for block in blocks:
            batch = {}
            digest = hashlib.sha256()
            for _ in range(block["validated_targets"]):
                line = stream.readline()
                digest.update(line)
                row = json.loads(line)
                batch[row["seed"]] = row["outcome"]
            require(digest.hexdigest() == block["audit_sha256"], "first-pass audit digest")
            yield batch
        require(not stream.read(1), "extra first-pass audit records")


def full_totals(data, config, examples, second_pass):
    plan = config["precision"]
    domain = plan["domains"]["full"]
    blocks = list(rows(data / "full-blocks.jsonl"))
    audits = audit_blocks(data, blocks)
    checkpoints = {}
    for name, size in (("nonterm", FULL_N_LOOKS[-1]), ("flagsj", plan["flag_N"]), ("term", plan["terminal_N"])):
        by_block = [b for b in blocks if b["stratum"] == name]
        block_size = plan["full_blocks"][name]
        require(len(by_block) * block_size == size, "wrong full block count")
        ledger = rows(data / f"{name}.jsonl.gz")
        total = Counter()
        first_pass = Counter()
        residual = unknown = 0
        for number, block in enumerate(by_block):
            first = number * block_size
            require(block["sample"]["seed"] == domain and block["sample"]["offsets"][name] == first, "full block range")
            tally = Counter()
            outside = Counter()
            audit = next(audits)
            for i in range(first, first + block_size):
                row = next(ledger)
                key, outcome = row["seed"], row["outcome"]
                require(key == f"{len(domain)}-{domain}-{name}-{i}" and row["stratum"] == name, "full draw identity")
                require(outcome in ("certified", "unreachable", "unresolved"), "unknown full outcome")
                prior = audit.pop(key)
                require(prior == ("unresolved" if "source" in row else outcome), "first-pass outcome conflict")
                first_pass[prior] += 1
                tally[outcome] += 1
                if name == "nonterm":
                    if row["screen_reason"] is None:
                        outside[outcome] += 1
                    else:
                        require(outcome == "unreachable", "screen exclusion disagrees with full proof")
                if key in examples:
                    witness = examples.pop(key)
                    require(outcome == "certified" and witness["sfen"] == row["sfen"] and
                            witness.get("flag") == row.get("flag"), "example disagrees with ledger")
                if "source" in row:
                    expected = second_pass.pop(key)
                    require(expected == (name, row["sfen"], row.get("flag"), outcome, row["proof"]),
                            f"second-pass proof disagrees with ledger for {key}")
            require(dict(tally) == block["counts"] and sum(tally.values()) == block["validated_targets"], "full block tally")
            total.update(tally)
            if name == "nonterm":
                require(block_size - sum(outside.values()) == block["matched"]["excluded"], "matched screen tally")
                require((outside["unreachable"], outside["unresolved"]) ==
                        (block["residual_nonmembers"], block["outside_unknown"]), "outside-screen tally")
                residual += outside["unreachable"]
                unknown += outside["unresolved"]
            stop = first + block_size
            if stop == size or (name == "nonterm" and stop in FULL_N_LOOKS):
                checkpoints[name, stop] = dict(counts=dict(total), residual=residual, unknown=unknown)
        require(next(ledger, None) is None, "extra full draws")
        print(f"{name} first audit: {dict(first_pass)}", file=sys.stderr)
    require(next(audits, None) is None, "extra first-pass blocks")
    require(not examples, "example missing from ledger")
    require(not second_pass, "second-pass proof missing from ledger")
    return checkpoints


def proof_index(data):
    index = {}
    for item in rows(data / "second-pass-games.jsonl.gz"):
        game, check = item["record"], item["verification"]
        sha = lambda value, sort: hashlib.sha256(json.dumps(value, sort_keys=sort).encode()).hexdigest()
        hashes = dict(route=game["route"], moves_sha256=sha(game["moves"], False),
                      record_sha256=sha(game, True), verification_sha256=sha(check, True))
        require(check["ok"] and hashes["record_sha256"] == check["record_sha256"], "game verification record")
        key = game["seed"]
        require(check["seed"] == key and key not in index, "duplicate or mismatched game")
        index[key] = (game["stratum"], game["sfen"], game.get("flag"), "certified", hashes)
    with ZipFile(data / "refutations.zip") as archive:
        for name in archive.namelist():
            if not name.endswith("/record.json"):
                continue
            record = json.loads(archive.read(name))
            key = record["seed"]
            replay = json.loads(archive.read(f"{key}/replay.json"))
            digest = hashlib.sha256(archive.read(f"{key}/nodes.jsonl.gz")).hexdigest()
            require(key not in index and name == f"{key}/record.json" and replay["seed"] == key, "refutation identity")
            require(replay["verified"] and record["exhausted"] and
                    digest == record["proof_sha256"] == replay["source_proof_sha256"], "refutation digest")
            hashes = dict(proof_sha256=digest, checks_sha256=replay["checks_sha256"])
            index[key] = (record["stratum"], record["sfen"], record.get("flag"), "unreachable", hashes)
    return index


def scaled(integer, multiplier, upper=False):
    numerator, unit = int(integer) * multiplier, 10**159
    endpoint = -(-numerator // unit) if upper else numerator // unit
    return f"{endpoint // 100000}.{endpoint % 100000:05d}"


def verify(data, replay):
    config_path = REPO / "experiments/jcsa-otb-20261118.json"
    config = read(config_path)
    manifest = read(data / "freeze.json")
    freeze_hash = hashlib.sha256((data / "freeze.json").read_bytes()).hexdigest()
    require(hashlib.sha256(config_path.read_bytes()).hexdigest() == manifest["sha256"]["config.json"], "settings hash")
    require(config["precision"]["full_N_looks"] == list(FULL_N_LOOKS) and
            config["precision"]["cheap_N_looks"] == [CHEAP_N, LATE_CHEAP_N], "registered looks")
    require(config["static_flag_population"] == {"draws": N_K, "successes": K_JCSA_1}, "static flag input")
    completion = read(data / "completion.json")
    require((completion["phase"], completion["reason"], completion["look"]) ==
            ("complete", "registered maximum reached", FULL_N_LOOKS[-1]), "stopping record")
    games = list(rows(data / "example-games.jsonl.gz"))
    require(len(games) == 3 and {g["stratum"] for g in games} == {"nonterm", "flagsj", "term"}, "example coverage")
    totals = full_totals(data, config, {g["seed"]: g for g in games}, proof_index(data))
    first, extra = screen_totals(data, config)
    flags = totals["flagsj", config["precision"]["flag_N"]]
    terminal = totals["term", config["precision"]["terminal_N"]]
    cn, ct = (int(config["expected_populations"][s]) for s in ("nonterm", "term"))
    output = io.StringIO(newline="")
    table = csv.writer(output, lineterminator="\n")
    table.writerow(("full_N", "cheap_N", "excluded", "N_certified", "N_unreachable", "N_unresolved",
                    "outside_unreachable", "outside_unresolved", "black_lower_1e164", "black_upper_1e164",
                    "either_lower_1e164", "either_upper_1e164"))
    for n in FULL_N_LOOKS:
        cheap, excluded = (CHEAP_N, first) if n < FULL_N_LOOKS[3] else (LATE_CHEAP_N, first + extra)
        ns = totals["nonterm", n]
        interval = full_interval(cheap, excluded, n, ns["residual"], ns["unknown"], flags["counts"],
                                 terminal["counts"], cn, ct, two_screen_looks=True)
        record = dict(N=n, cheap_N=cheap, E=excluded, nonterm=ns, flags=flags, terminal=terminal,
                      freeze_sha256=freeze_hash, interval=interval)
        stored, = (data / "checkpoints").glob(f"*-production-look-{n}.json")
        require(record == read(stored), f"checkpoint mismatch at {n}")
        endpoints = [scaled(interval[key], m, upper) for m in (1, 2)
                     for key, upper in (("lower_integer", False), ("upper_integer", True))]
        table.writerow((n, cheap, excluded, *(ns["counts"][k] for k in ("certified", "unreachable", "unresolved")),
                        ns["residual"], ns["unknown"], *endpoints))
    require(output.getvalue().encode() == (data / "registered-intervals.csv").read_bytes(), "published CSV mismatch")
    if replay:
        from count.sfen import parse
        from jcsa.native_audit import NativeAudit
        checker = NativeAudit()
        try:
            games.extend(item["record"] for item in rows(data / "second-pass-games.jsonl.gz"))
            for game in games:
                board = parse(game["sfen"])[0]
                flag = tuple(game["flag"]) if game.get("flag") else None
                ok, reason = checker.verify(game["moves"], board, game["stratum"], flag)
                require(ok and checker.view(board, flag=flag)[0] == game["terminal"], reason)
            print(f"Replayed {len(games)} complete production games", file=sys.stderr)
        finally:
            checker.close()
    sys.stdout.write(output.getvalue())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", action="store_true", help="also replay all included proof games with the native checker")
    parser.add_argument("--archive", type=Path, help="use a locally downloaded copy of the release evidence")
    args = parser.parse_args()
    cache = REPO / "out" / TAG
    cache.mkdir(parents=True, exist_ok=True)
    if args.archive is None:
        archive = release_archive(cache)
    else:
        archive = args.archive
        require(archive_hash(archive) == ARCHIVE_SHA256, "supplied evidence checksum mismatch")
    with TemporaryDirectory(dir=cache) as unpacked:
        with ZipFile(archive) as bundle:
            bundle.extractall(unpacked)
        verify(Path(unpacked), args.replay)
