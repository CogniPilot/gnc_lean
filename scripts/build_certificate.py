"""Build one Lake certificate with bounded parallelism and resource diagnostics.

This does not replace the complete library/axiom audit. Lake retains its normal
source and dependency trace checks; each successful CI step is cached separately.
"""
import argparse
import subprocess
import threading


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('module', choices=[
        'GNC.Applications.OrbitalComparison.PointingCapBernsteinData',
        'GNC.Applications.OrbitalComparison.BernsteinData.STT8Time10',
        'GNC.Applications.OrbitalComparison.BernsteinData.STT8Time12'])
    args = parser.parse_args()
    done = threading.Event()

    def monitor():
        while not done.wait(30):
            print(f'Still building {args.module}', flush=True)
            subprocess.run(['free', '-m'], check=False)
            subprocess.run(['ps', '-C', 'lean', '-o', 'pid,rss,etime,args',
                            '--sort=-rss'], check=False)

    worker = threading.Thread(target=monitor, daemon=True)
    worker.start()
    try:
        result = subprocess.run(['lake', 'build', args.module])
    finally:
        done.set()
        worker.join()
    raise SystemExit(result.returncode if result.returncode >= 0 else 128-result.returncode)


if __name__ == '__main__':
    main()
