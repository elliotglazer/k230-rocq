"""Fetch the exact upstream commit required by manifest.json."""
from pathlib import Path
import argparse
import json
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, default=ROOT / ".deps/jeff-busy-beaver")
    args = parser.parse_args()
    spec = json.loads((ROOT / "manifest.json").read_text(encoding="utf-8"))["reference"]
    dest = args.destination.resolve()
    dest.parent.mkdir(parents=True, exist_ok=True)
    if not dest.exists():
        subprocess.run(["git", "init", str(dest)], check=True)
        subprocess.run(["git", "-C", str(dest), "remote", "add", "origin", spec["url"]], check=True)
    elif not (dest / ".git").is_dir():
        raise RuntimeError("The destination exists and is not a Git checkout; refusing to replace it.")
    status = subprocess.check_output(["git", "-C", str(dest), "status", "--porcelain"], text=True)
    if status.strip():
        raise RuntimeError("The destination has local changes; refusing to change its checkout.")
    subprocess.run(["git", "-C", str(dest), "fetch", "--depth", "1", spec["url"], spec["commit"]], check=True)
    subprocess.run(["git", "-C", str(dest), "checkout", "--detach", spec["commit"]], check=True)
    actual = subprocess.check_output(["git", "-C", str(dest), "rev-parse", "HEAD"], text=True).strip()
    if actual != spec["commit"]:
        raise RuntimeError("Fetched checkout has the wrong commit.")
    print(f"Pinned dependency ready at {dest}")


if __name__ == "__main__":
    main()
