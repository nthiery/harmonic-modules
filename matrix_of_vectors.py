#!/usr/bin/env python
# -*- coding: utf-8 -*-

import operator

from utilities import items_of_vector

from sage.structure.parent import Parent
from sage.combinat.ranker import on_fly
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector


class MatrixOfVectors:
    """
    A mutable data structure representing a collection of vectors as a matrix

    EXAMPLES::

        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: x,y,z = R.gens()
        sage: M = MatrixOfVectors([x, 2*z, x*y+z, 2*x+z+x*y]); M
        A 4x3 matrix of vectors in Multivariate Polynomial Ring in x, y, z over Rational Field
        sage: M._matrix
        [1 0 0]
        [0 2 0]
        [0 1 1]
        [2 1 1]


    .. NOTE::

        - Currently, adding a new vector is linear in the size of the matrix.
          This could probably be fixed by changing the matrix in place.
        - Currently, the matrix is dense
    """
    def __init__(self, vectors=None, ambient=None, stats={}):
        if vectors is None and not isinstance(ambient, Parent):
            vectors = ambient
            ambient = None
        if ambient is None:
            if vectors is not None:
                ambient = vectors[0].parent()
        self._ambient = ambient
        self._base_ring = ambient.base_ring()
        self._rank, self._unrank = on_fly()
        self._matrix = matrix(self._base_ring, 0, 0)
        self._basis = []
        self._words = []
        self._is_echelon = True
        stats.setdefault("add_vector", 0)
        stats.setdefault("extend", 0)
        stats.setdefault("zero", 0)
        stats.setdefault("dimension", 0)
        self._stats = stats
        if vectors:
            for v in vectors:
                self.add_vector(v)

    def __repr__(self):
        """

        EXAMPLES::

            sage: E = CombinatorialFreeModule(QQ, [1,2,4,8,16])
            sage: M = EchelonMatrixOfVectors(ambient=E); M
            A 0x0 echelon matrix of vectors in Free module generated by {1, 2, 4, 8, 16} over Rational Field
            sage: M.extend(E.an_element())
            True
            sage: M
            A 1x3 echelon matrix of vectors in Free module generated by {1, 2, 4, 8, 16} over Rational Field
        """
        m = self._matrix
        return "A %sx%s matrix of vectors in %s"%(m.nrows(), m.ncols(), self.ambient())

    def ambient(self):
        return self._ambient

    def plain_vector(self, v):
        """
        Return `v` as a plain vector

        INPUT:

        - ``v`` -- an element of the ambient space

        Invariant: when it's returned, the length of the vector is the
        number of basis elements ranked, which is at least the number
        of columns of the matrix.
        """
        # TODO:
        # - optimize this
        # - implement and use a generic api to recover the items
        if not self._ambient.is_parent_of(v):
            raise ValueError("Expected vector in %s; got %s"%(self._ambient, v))
        rank = self._rank
        d = dict((rank(i), c) for i, c in items_of_vector(v))
        return vector(self._base_ring, len(self._rank.cache), d, sparse=False)

    def vector(self, v):
        R = self.ambient()
        unrank = self._unrank
        # TODO: this only works for polynomials!
        return R.sum(v[i]* R.monomial(*unrank(i)) for i in range(len(v)))

    def vectors(self):
        return tuple(self.vector(v) for v in self._matrix)

    def _add_vector_to_matrix(self, m, v): # append?
        r = self.plain_vector(v)
        if len(r) > m.ncols():
            m = m.augment(matrix(self._base_ring, m.nrows(), len(r)-m.ncols()))
        return m.stack(r)

    def add_vector(self, v):
        """
        Add `v` at the bottom of ``self``
        """
        self._stats["add_vector"] += 1
        self._is_echelon = False
        self._matrix = self._add_vector_to_matrix(self._matrix, v)

    def cardinality(self): # or __len__, nrows ??? or dimension in EchelonMatrixOfVectors ???
        return self._matrix.nrows()

class EchelonMatrixOfVectors(MatrixOfVectors):
    """
    A mutable data structure representing a collection of vectors in row echelon form
    """

    def __repr__(self):
        """

        EXAMPLES::

            sage: E = CombinatorialFreeModule(QQ, [1,2,4,8,16])
            sage: M = EchelonMatrixOfVectors(ambient=E); M
            A 0x0 echelon matrix of vectors in Free module generated by {1, 2, 4, 8, 16} over Rational Field
            sage: M.extend(E.an_element())
            True
            sage: M
            A 1x3 echelon matrix of vectors in Free module generated by {1, 2, 4, 8, 16} over Rational Field
        """
        m = self._matrix
        return "A %sx%s echelon matrix of vectors in %s"%(m.nrows(), m.ncols(), self.ambient())

    def extend(self, v, word=None):
        self._stats["extend"] += 1
        if not v:
            self._stats["zero"] += 1
            return False
        assert self._is_echelon
        m = self._add_vector_to_matrix(self._matrix, v)
        m.echelonize()
        if m[-1]:
            self._stats['dimension'] += 1
            self._matrix = m
            self._basis.append(v)
            if word is not None:
                self._words.append(word)
            return True
        return False

def annihilator_basis(B, S, action=operator.mul, side='right', ambient=None):
    """
    A generalization of :meth:`Modules.FiniteDimensional.WithBasis.ParentMethods.annihilator_basis`

    Return a basis of the annihilator of a finite set of elements in the span of ``B``

    INPUT:

    - ``B`` -- a finite iterable of vectors (linearly independent???)

    - ``S`` -- a finite iterable of objects

    - ``action`` -- a function (default: :obj:`operator.mul`)

    - ``side`` -- 'left' or 'right' (default: 'right'):
      on which side of ``self`` the elements of `S` acts.

    See :meth:`annihilator` for the assumptions and definition
    of the annihilator.

    EXAMPLES:

    By default, the action is the standard `*` operation. So
    our first example is about an algebra::

        sage: F = FiniteDimensionalAlgebrasWithBasis(QQ).example(); F
        An example of a finite dimensional algebra with basis:
        the path algebra of the Kronecker quiver
        (containing the arrows a:x->y and b:x->y) over Rational Field
        sage: x,y,a,b = F.basis()

    In this algebra, multiplication on the right by `x`
    annihilates all basis elements but `x`::

        sage: x*x, y*x, a*x, b*x
        (x, 0, 0, 0)

    So the annihilator is the subspace spanned by `y`, `a`, and `b`::

        sage: annihilator_basis(F.basis(), [x])
        (y, a, b)

    The same holds for `a` and `b`::

        sage: x*a, y*a, a*a, b*a
        (a, 0, 0, 0)
        sage: annihilator_basis(F.basis(), [a])
        (y, a, b)

    On the other hand, `y` annihilates only `x`::

        sage: annihilator_basis(F.basis(), [y])
        (x,)

    Here is a non trivial annihilator::

        sage: annihilator_basis(F.basis(), [a + 3*b + 2*y])
        (-1/2*a - 3/2*b + x,)

    Let's check it::

        sage: (-1/2*a - 3/2*b + x) * (a + 3*b + 2*y)
        0

    Doing the same calculations on the left exchanges the
    roles of `x` and `y`::

        sage: annihilator_basis(F.basis(), [y], side="left")
        (x, a, b)
        sage: annihilator_basis(F.basis(), [a], side="left")
        (x, a, b)
        sage: annihilator_basis(F.basis(), [b], side="left")
        (x, a, b)
        sage: annihilator_basis(F.basis(), [x], side="left")
        (y,)
        sage: annihilator_basis(F.basis(), [a+3*b+2*x], side="left")
        (-1/2*a - 3/2*b + y,)

    By specifying an inner product, this method can be used to
    compute the orthogonal of a subspace::

        sage: x,y,a,b = F.basis()
        sage: def scalar(u,v): return vector([sum(u[i]*v[i] for i in F.basis().keys())])
        sage: annihilator_basis(F.basis(), [x+y, a+b], scalar)
        (x - y, a - b)

    By specifying the standard Lie bracket as action, one can
    compute the commutator of a subspace of `F`::

        sage: annihilator_basis(F.basis(), [a+b], action=F.bracket)
        (x + y, a, b)

    In particular one can compute a basis of the center of the
    algebra. In our example, it is reduced to the identity::

        sage: annihilator_basis(F.basis(), F.algebra_generators(), action=F.bracket)
        (x + y,)

    But see also
    :meth:`FiniteDimensionalAlgebrasWithBasis.ParentMethods.center_basis`.
    """
    if side == 'right':
        action_left = action
        action = lambda b,s: action_left(s, b)
    B = list(B)
    S = list(S)
    if ambient is None:
        ambient = action(S[0], B[0]).parent()
    mat = matrix(ambient.base_ring(), len(B), 0)

    for s in S:
        mat = mat.augment(
            MatrixOfVectors([action(s, b) for b in B], ambient=ambient)._matrix)

    return tuple(sum(c * B[i] for i,c in v.iteritems())
                 for v in mat.left_kernel().basis())

