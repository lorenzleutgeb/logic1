import os
from pathlib import Path

import gmpy2
from Cython.Build import cythonize
from setuptools import Extension, setup


setup(
    ext_modules=cythonize([
        Extension(
            'logic1.theories.RCF.range',
            sources=['logic1/theories/RCF/range.pyx'],
            include_dirs=[str(Path(gmpy2.__file__).parent)],
            libraries=['gmp'],
        ),
    ], annotate=os.environ.get('CYTHON_ANNOTATE') == '1'),
)
