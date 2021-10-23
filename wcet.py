#!/usr/bin/env python3

from z3 import Solver, parse_smt2_file, Int, sat


def binary_search(lb, ub, s, makespan, epsilon=1e-6):
    if (ub - lb <= epsilon):
        s.check()
        return s.model()
    else:
        half = lb + ((ub - lb)/2.0)
        s.push()
        s.add(makespan >= half, makespan <= ub)
        ret = s.check()
        s.pop()
        if ret == sat:
            return binary_search(half, ub, s, makespan, epsilon)
        else:
            return binary_search(lb, half, s, makespan, epsilon)


def main(fname):
    eqn = parse_smt2_file(fname)
    W = Int('W')
    s = Solver()
    s.add(eqn)
    # print(s)
    s.check()
    print('Model: ', binary_search(0, 10000000, s, W))


if __name__ == '__main__':
    main('binarySearch.smt2')
