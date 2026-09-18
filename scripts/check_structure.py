"""Check complete GNC exports, core/application dependencies and document links."""
from pathlib import Path
import re
import os
import sys


def structure_errors(root):
    modules = {}
    for path in (root/'GNC').rglob('*.lean'):
        relative = path.relative_to(root)
        if relative.parts[1] == 'Verification' or relative == Path('GNC/Verification.lean'):
            relative = path.relative_to(root/'GNC')
        modules[str(relative.with_suffix('')).replace('/', '.')] = path
    errors, edges = [], {}
    for directory, children, files in os.walk(root):
        children[:] = [name for name in children if name not in {'.git', '.lake', '.direnv', 'source', '__pycache__'}]
        for name in files:
            path = Path(directory, name)
            if path.suffix == '.lean' and not path.is_relative_to(root/'GNC'):
                errors.append(f'Proof outside GNC: {path.relative_to(root)}')
    for required in ['GNC.All', 'Verification']:
        if required not in modules:
            errors.append(f'Missing root module: {required}')
            modules[required] = root/(required.replace('.', '/')+'.lean')
    for module, path in modules.items():
        if not path.exists():
            errors.append(f'Missing root module: {module}')
            edges[module] = []
            continue
        imports = re.findall(r'^import (\S+)', path.read_text(), re.M)
        edges[module] = [x for x in imports if x in modules]
        for dependency in imports:
            if dependency.startswith(('GNC', 'Verification')) and dependency not in modules:
                errors.append(f'{path.relative_to(root)}: missing module {dependency}')
            if module.startswith('GNC') and dependency.startswith('Verification'):
                errors.append(f'Library imports audit tooling: {module} -> {dependency}')
            if (module.startswith('GNC.') and not module.startswith('GNC.Tools.')
                    and dependency.startswith('GNC.Tools.')):
                errors.append(f'Mathematics imports executable tooling: {module} -> {dependency}')
            if (module.startswith('GNC.') and module != 'GNC.All'
                    and not module.startswith('GNC.Tools.')
                    and not (module == 'GNC.Applications' or module.startswith('GNC.Applications.'))
                    and dependency.startswith('GNC.Applications')):
                errors.append(f'Core imports an application: {module} -> {dependency}')
    visiting, seen = set(), set()

    def visit(module):
        if module in visiting:
            errors.append(f'Import cycle: {module}')
            return
        if module in seen:
            return
        visiting.add(module)
        for dependency in edges[module]:
            visit(dependency)
        visiting.remove(module)
        seen.add(module)

    visit('GNC.All')
    for module in modules:
        if module.startswith('GNC') and not module.startswith('GNC.Tools.') and module not in seen:
            errors.append(f'Not exported by GNC: {module}')
    visit('Verification')
    for module in modules:
        if module not in seen:
            errors.append(f'Not covered by default verification target: {module}')
    for path in [root/'README.md', *root.glob('docs/**/*.md'), *root.glob('GNC/**/*.md'),
                 *root.glob('Papers/**/*.md')]:
        if not path.exists():
            continue
        for target in re.findall(r'\[[^\]]*\]\(([^ )]+)\)', path.read_text()):
            if target.startswith(('http:', 'https:', 'mailto:', '#')):
                continue
            if not (path.parent/target.split('#')[0]).exists():
                errors.append(f'{path.relative_to(root)}: missing link {target}')
    return errors, len(modules)


def main():
    errors, count = structure_errors(Path(__file__).resolve().parent.parent)
    if errors:
        print('\n'.join(errors))
        sys.exit(1)
    print(f'Structure check passed: {count} modules; all proofs exported by GNC; '
          'core has no application imports; local Markdown links resolve.')


if __name__ == '__main__':
    main()
