"""Keep generated build debris and Nix result links out of the source tree."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent.parent


def main():
    errors = []
    tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    for name in filter(None, tracked):
        path = ROOT/name
        if not path.exists():  # A staged removal is checked by Git after staging.
            continue
        if any(part in {'.lake', '.direnv', '__pycache__'} for part in path.relative_to(ROOT).parts):
            errors.append(f'Tracked build artifact: {name}')
        if path.is_symlink() and str(path.readlink()).startswith('/nix/store/'):
            errors.append(f'Tracked Nix result link: {name}')
    for path in ROOT.glob('result*'):
        if path.is_symlink():
            errors.append(f'Root build link: {path.name}; use --out-link .lake/TARGET or --no-link')
    if errors:
        raise SystemExit('\n'.join(errors))
    print('Repository check passed: no root Nix links or tracked build caches.')


if __name__ == '__main__':
    main()
