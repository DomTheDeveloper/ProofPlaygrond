"""Check both independent classifications of every support of an 11-smooth integer."""
from argparse import ArgumentParser
from itertools import combinations

from fixed_support import classify
from integer_certificate import exhaustive


def main(method):
    primes = (2, 3, 5, 7, 11)
    node_count = 0
    for size in range(len(primes) + 1):
        for support in combinations(primes, size):
            if method == 'rational':
                points, rays, visits = classify(support)
            else:
                points, rays, visits, _ = exhaustive(support)
            expected_points = [()] if not support else []
            expected_rays = [(2, ())] if support == (2,) else []
            if points != expected_points or rays != expected_rays:
                raise AssertionError((support, points, rays))
            node_count += sum(visits)
            print(support, points, rays, visits, flush=True)
    print(f'{method}: all 32 supports certified; {node_count} search nodes.')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('method', choices=('rational', 'integer'))
    main(parser.parse_args().method)
