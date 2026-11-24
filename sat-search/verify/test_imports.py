"""Module-resolution guard (verify/AUDIT.md, module shadowing). <repo>/.scratch-sat holds vendored python-sat
and also scratch scripts; one of them (port_certificate_construction.py) has the same name as a repository
module. cube_search.py and verify/reference.py now append .scratch-sat to sys.path instead of prepending it.
Expected: after importing cube_search, every module name that exists both in .scratch-sat and in the
repository resolves to the repository copy, and pysat resolves to the vendored copy.
Run: python verify/test_imports.py"""
import glob, importlib.util, os, sys, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
SAT = os.path.dirname(HERE)
REPO = os.path.dirname(SAT)
SCRATCH = os.path.join(REPO, '.scratch-sat')
sys.path.insert(0, SAT)
sys.path.insert(0, os.path.join(SAT, 'experiments'))
import cube_search  # noqa: E402  (performs the path setup under test)


class ModuleResolution(unittest.TestCase):
    def test_repository_modules_win(self):
        scratch = {os.path.splitext(os.path.basename(p))[0] for p in glob.glob(os.path.join(SCRATCH, '*.py'))}
        importable = (SAT, os.path.join(SAT, 'experiments'), os.path.join(SAT, 'verify'), os.path.join(SAT, 'theory'))
        repo = {os.path.splitext(os.path.basename(p))[0] for d in importable for p in glob.glob(os.path.join(d, '*.py'))}
        collisions = sorted(scratch & repo)
        for name in collisions:
            spec = importlib.util.find_spec(name)
            self.assertIsNotNone(spec, name)
            self.assertFalse(os.path.abspath(spec.origin).startswith(os.path.abspath(SCRATCH)),
                             f'{name} resolves to the scratch copy {spec.origin}')
        print(f'\n  colliding names checked: {collisions}')

    def test_vendored_pysat(self):
        import pysat
        self.assertTrue(os.path.abspath(pysat.__file__).startswith(os.path.abspath(SCRATCH)), pysat.__file__)

    def test_solver_imports_resolve_in_repository(self):
        required = ('partial_ordered', 'monotone_interface', 'port_certificates', 'provider_certificates')
        optional = ('provider_capacity',)          # imported only by newer versions of cube_search.py
        for name in required + optional:
            mod = sys.modules.get(name)
            if mod is None and name in optional:
                continue
            self.assertIsNotNone(mod, name)
            self.assertTrue(os.path.abspath(mod.__file__).startswith(os.path.abspath(SAT)), mod.__file__)


if __name__ == '__main__':
    unittest.main(verbosity=2)
