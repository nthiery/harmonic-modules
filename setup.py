## -*- encoding: utf-8 -*-
import os
import sys
from setuptools import setup, Extension
from codecs import open # To open the README file with proper encoding
from setuptools.command.test import test as TestCommand # for tests
from Cython.Build import cythonize


# Get information from separate files (README, VERSION)
def readfile(filename):
    with open(filename,  encoding='utf-8') as f:
        return f.read()

# For the tests
class SageTest(TestCommand):
    def run_tests(self):
        errno = os.system("sage -t funcpersist.py matrix_of_vectors.py subspace.py diagram.py diagonal_polynomial_ring.py harmonic.py polarization_space.py")
        if errno != 0:
            sys.exit(1)

setup(
    name = "harmonic_module",
    version = readfile("VERSION").strip(), # the VERSION file is shared with the documentation
    description='Computing the bicharacter of diagonal harmonic polynomials',
    long_description = readfile("README.rst"), # get the long description from the README
    url='https://github.com/nthiery/harmonic-modules',
    author='Pauline Hubert, Nicolas M. Thiéry',
    author_email='Nicolas.Thiery@u-psud.fr',
    license='GPLv2+', # This should be consistent with the LICENCE file
    classifiers=[
      # How mature is this project? Common values are
      #   3 - Alpha
      #   4 - Beta
      #   5 - Production/Stable
      'Development Status :: 4 - Beta',
      'Intended Audience :: Science/Research',
      'Topic :: Software Development :: Build Tools',
      'Topic :: Scientific/Engineering :: Mathematics',
      'License :: OSI Approved :: GNU General Public License v2 or later (GPLv2+)',
      'Programming Language :: Python :: 2.7',
    ], # classifiers list: https://pypi.python.org/pypi?%3Aaction=list_classifiers
    keywords = "",
    py_modules=['funcpersist',
                'matrix_of_vectors', 'subspace',
                'diagram',
                'diagonal_polynomial_ring', 'harmonic', 'polarization_space',
               ],
    cmdclass = {'test': SageTest}, # adding a special setup command for tests
    setup_requires   = ['sage-package'],
    install_requires = ['sage-package', 'sphinx'],

    ext_modules=cythonize([
        Extension('utilities',
                  sources=['utilities.pyx'],
                  #language='c++',             # generate C++ code
                  #extra_compile_args=extra_compile_args
                  ),
        Extension('antisymmetric_utilities',
                  sources=['antisymmetric_utilities.pyx'],
                  #language='c++',             # generate C++ code
                  #extra_compile_args=extra_compile_args
                  )
        ]),
)
