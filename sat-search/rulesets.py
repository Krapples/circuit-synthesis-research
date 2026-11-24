"""Canonical rule sets shared by the drivers (single source; verify/test_rulesets.py guards against drift).

FAST_RULES is the --fast set of cube_search.py main() without the cube-selection and encoding switches it
also turns on there (symmetry, fanout, readonce), which drivers pass positionally to run_cube.
fast_flags(monotone) returns the run_cube flag dictionary the drivers used before this module existed
(identical contents; monotone adds nonot)."""

FAST_RULES = ('sens', 'units', 'usens', 'bypass', 'elim', 'elimclosure', 'signeddom', 'recursivebounds',
              'notbypass', 'recclosure', 'identifybounds', 'fanoutelim', 'pairro', 'colorbounds', 'sharecolor',
              'colorbudget')
FAST_CLI = ('symmetry', 'fanout', 'readonce') + FAST_RULES     # the switches main() sets for --fast
RECDEPTH = 2


def fast_flags(monotone=True):
    flags = {k: True for k in FAST_RULES}
    flags['recdepth'] = RECDEPTH
    if monotone:
        flags['nonot'] = True
    return flags
