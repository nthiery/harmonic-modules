Computing the bicharacter of diagonal harmonic polynomials
==========================================================

.. image:: https://mybinder.org/badge.svg
   :target: https://mybinder.org/v2/gh/nthiery/harmonic-modules/demo.ipynb

The main goal of this project  is to compute the character of diagonal
harmonic polynomials on $k$ rows of $n$ variables w.r.t. the action of
$GL_k$ and $S_n$. See `<DiagonalCharacter.ipynb>`_
for explanations, as well as those `slides <https://mybinder.org/v2/gh/nthiery/harmonic-modules/master?filepath=talk.ipynb>`_ of a talk on the topic (slow to start, but then you can play with the examples live!).

Dependencies: the `SageMath <http://sagemath.org>`_ open source mathematical system

License: GPL

## Subspace computation facilities

The code for this project includes generic facilities for computing
subspaces of general Sage vector spaces like polynomial rings. See
utilities.pyx, matrix_of_vectors.py, subspace.py.

This code is being extracted and refactored as a dedicated
Sage package, to be eventually integrated into Sage:

    https://github.com/darijgr/sage-subspace/

Don't edit the corresponding files in this repo; it will soon go away
in favor of using sage-subspace.
