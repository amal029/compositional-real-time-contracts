#!/usr/bin/env python3

from z3 import Solver, parse_smt2_file, Int


def main(fname):
    eqn = parse_smt2_file(fname)
    W = Int('W')
    s = Solver()
    s.add(eqn)
    print(s)
    s.check()
    print('Found WCET for program: %s : %s ' % (fname, s.model()[W]))


if __name__ == '__main__':
    main('prog1.smt2')
