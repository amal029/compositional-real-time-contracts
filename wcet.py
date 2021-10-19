#!/usr/bin/env python3

from z3 import Solver, sat, parse_smt2_file, Int


def maximise(lb, ub, s, makespan, epsilon=1e-12):
    if (ub - lb <= epsilon):
        s.check()
        return s.model()[makespan]
    else:
        half = lb + ((ub - lb)/2.0)
        s.push()
        s.add(makespan >= half, makespan <= ub)
        ret = s.check()
        s.pop()
        if ret == sat:
            return maximise(half, ub, s, makespan, epsilon)
        else:
            return maximise(lb, half, s, makespan, epsilon)


def main(fname):
    eqn = parse_smt2_file(fname)
    W = Int('W')
    s = Solver()
    s.add(eqn)
    print(s)
    s.check()
    print('Found WCET for program: %s : %s ' % (fname, s.model()[W]))


if __name__ == '__main__':
    main('prog2.smt2')
