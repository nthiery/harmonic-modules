#!/usr/bin/env python
# -*- coding: utf-8 -*-

import functools

from sage.misc.constant_function import ConstantFunction
from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.parent import Parent
from sage.combinat.partition import Partition, Partitions
from sage.rings.semirings.non_negative_integer_semiring import NN
from sage.rings.rational_field import QQ
from sage.combinat.free_module import CombinatorialFreeModule

from matrix_of_vectors import *


class Subspace(object):
    """
    Construct a subspace from generators and linear operators

    INPUT:

    - ``generators`` -- a list of vectors in some ambient vector space `V`
    - ``operators`` -- a list of linear endomorphism `V` (default: ``[]``)

    - ``hilbert_parent`` -- a function that, g
    
    iven the dimensions of the subspaces
      given as a dictionary { degree: dim } returns the hilbert polynomial

    Return the smallest subspace of `V` containing ``generators`` and
    stable under the action of the operators.

    EXAMPLES::

        sage: E = CombinatorialFreeModule(QQ, [1,2,4,8,16])
        sage: v = E.an_element(); v
        2*B[1] + 2*B[2] + 3*B[4]
        sage: F = Subspace([v, v], [])
        sage: F.dimension()
        1

        sage: B = E.basis()
        sage: F = Subspace([B[1]-B[2], B[2]-B[4], B[1]-B[4]])
        sage: F.dimension()
        2
        sage: F.matrix()
        [ 1  0 -1]
        [ 0  1 -1]

        sage: E = CombinatorialFreeModule(QQ, [1,2,4,8,16])
        sage: B = E.basis()
        sage: phi = E.module_morphism(lambda i: B[i]+B[2*i] if i <= 8 else E.zero(), codomain=E)
        sage: F = Subspace([phi(B[1])], [phi])
        sage: F.dimension()
        4
        sage: F.matrix()
        [ 1  0  0  0 -1]
        [ 0  1  0  0  1]
        [ 0  0  1  0 -1]
        [ 0  0  0  1  1]

    Computing a subspace of a multivariate polynomial ring::

        sage: P = QQ['x,y,z']
        sage: x,y,z = P.gens()
        sage: F = Subspace([x-y, y-z, x-z])
        sage: F.dimension()
        2
        sage: F.matrix()
        [ 1  0 -1]
        [ 0  1 -1]

    The derivatives of the Van-der-Monde determinant in `n` variables
    spans a space of dimension `n!`::

        sage: Delta = (x-y)*(y-z)*(x-z)
        sage: F = Subspace([Delta], [attrcall("derivative", x) for x in P.gens()])
        sage: F.dimension()
        6

    Computing subalgebras and modules in the algebra of the symmetric
    group::

        sage: S = SymmetricGroup(4)
        sage: A = S.algebra(QQ)
        sage: F = Subspace([A.one()], [functools.partial(operator.mul, A.jucys_murphy(i)) for i in range(1,4)])
        sage: F.dimension()
        4
        sage: F.matrix()
        [1 0 0 0 0 0]
        [0 1 1 0 0 0]
        [0 0 0 1 1 0]
        [0 0 0 0 0 1]

        sage: T = StandardTableaux(4)
        sage: def young_idempotent(t):
        ....:     return A.sum_of_terms((S(sigma), sigma.sign()) for sigma in t.column_stabilizer()) * \
        ....:            A.sum_of_monomials(S(sigma) for sigma in t.row_stabilizer())
        sage: for t in T:
        ....:     print(t.shape(), t.shape().dimension(), \
        ....:          Subspace([young_idempotent(t)], \
        ....:                   [functools.partial(operator.mul, s) for s in A.algebra_generators()]).dimension())
        [4] 1 1
        [3, 1] 3 3
        [3, 1] 3 3
        [3, 1] 3 3
        [2, 2] 2 2
        [2, 2] 2 2
        [2, 1, 1] 3 3
        [2, 1, 1] 3 3
        [2, 1, 1] 3 3
        [1, 1, 1, 1] 1 1


    Redoing the derivatives of the Van-der-Monde determinant in `n` variables
    as a graded subspace::

        sage: def add_degrees(d1, d2):
        ....:     d = d1 + d2
        ....:     if d < 0: raise ValueError("Negative degree")
        ....:     return d
        sage: P = QQ['x,y,z']
        sage: x,y,z = P.gens()
        sage: Delta = (x-y)*(y-z)*(x-z)
        sage: F = Subspace(generators={3:[Delta]},
        ....:              operators={-1:[attrcall("derivative", x) for x in P.gens()]},
        ....:              add_degrees=add_degrees)
        sage: F.dimension()
        6
        sage: F.dimensions()
        {0: 1, 1: 2, 2: 2, 3: 1}
        sage: F.hilbert_polynomial()
        q^3 + 2*q^2 + 2*q + 1

        sage: load("young_idempotent.py")
        sage: P = QQ['x,y,z,t']
        sage: x,y,z,t = P.gens()
        sage: Delta = apply_young_idempotent(x^3*y^2*z, Partition([1,1,1,1]))
        sage: F = Subspace(generators={6:[Delta]},
        ....:              operators={-1:[attrcall("derivative", x) for x in P.gens()]},
        ....:              add_degrees=add_degrees)
        sage: F.hilbert_polynomial()
        q^6 + 3*q^5 + 5*q^4 + 6*q^3 + 5*q^2 + 3*q + 1
        sage: sage.combinat.q_analogues.q_factorial(4)
        q^6 + 3*q^5 + 5*q^4 + 6*q^3 + 5*q^2 + 3*q + 1
    """

    # Invariants:
    #
    # self._todo contains a list of tuples (v, op, d, word) where `v`
    # is a vector on which we need to apply op to produce an element
    # w of degree d and "reduced word" `word`

    def __init__(self, generators, operators={},
                 add_degrees=operator.add,
                 extend_word=ConstantFunction([]),
                 hilbert_parent=None,
                 degree=None,
                 ambient=None,
                 verbose=False):
        self._stats={}
        self._verbose=verbose

        if self._verbose is not False:
            import tqdm
            if isinstance(self._verbose, tqdm.tqdm):
                self._bar = self._verbose
            else:
                self._bar = tqdm.tqdm(leave=True, unit=" extensions")
            if isinstance(self._verbose, str):
                self._bar.set_description(self._verbose)

        self._degree = degree
        if not isinstance(generators, dict):
            if self._degree is None:
                generators = {0: generators}
            else:
                gens = dict()
                for g in generators:
                    d = self._degree(g)
                    gens.setdefault(d, [])
                    gens[d].append(g)
                generators = gens

        self._generators = generators

        if ambient is not None:
            assert all( ambient.is_parent_of(g) for gens in generators.values() for g in gens )
        else:
            ambient = {g.parent() for gens in generators.values() for g in gens}
            assert len(ambient) == 1
            ambient = ambient.pop()
        self._ambient = ambient
        self._base_ring = ambient.base_ring()

        if hilbert_parent is None:
            if generators.keys()[0] in NN:
                hilbert_parent = QQ['q']
        self._hilbert_parent = hilbert_parent

        if not isinstance(operators, dict):
            operators = {0: operators}
        self._operators = operators

        self._bases = {}
        self._todo = []
        self._add_degrees = add_degrees
        self._extend_word = extend_word
        for d, gens in generators.iteritems():
            basis = EchelonMatrixOfVectors(ambient=self._ambient, stats=self._stats)
            for g in gens:
                if basis.extend(g):
                    self.todo(g, d, [])
            self._bases[d] = basis

    
    def __getstate__(self):
        return {}
    
    def todo(self, vector, d1, word):
        todo = self._todo
        for d2, ops in self._operators.iteritems():
            try:
                d3 = self._add_degrees(d1, d2)
            except ValueError:
                continue
            for op in ops:
                new_word = self._extend_word(word, op)
                if new_word is not None:
                    todo.append((vector, op, d3, new_word))

    def dimension(self):
        """

        """
        self.finalize()
        return sum(basis.cardinality() for basis in self._bases.values())

    def basis(self):
        self.finalize()
        basis = {}
        for i, val in self._bases.iteritems() : 
            if val.vectors() != () :
                basis[i] = val.vectors()
        #return sum((basis.vectors() for basis in self._bases.values()), ())
        return basis

    def hilbert_polynomial(self):
        return self._hilbert_parent(self.dimensions())

    def dimensions(self):
        self.finalize()
        return {d: basis.cardinality() for d, basis in self._bases.iteritems()}

    def matrix(self):
        self.finalize()
        assert self._bases.keys() == [0] # only handle the non graded case
        return self._bases[0]._matrix

    def extend(self, v, d=None, word=None):
        if d is None and self._degree is not None:
            d = self._degree(v)
        if d not in self._bases:
            self._bases[d] = EchelonMatrixOfVectors(ambient=self._ambient, stats=self._stats)
        if self._bases[d].extend(v):
            self.todo(v, d, word)
        if self._verbose is not False:
            self._bar.update()
            self._bar.set_postfix({'todo': len(self._todo), 'dimension': self._stats['dimension'],  'zero': self._stats['zero']})

    @cached_method
    def finalize(self):   # compute?
        todo = self._todo
        if not todo:
            return
        while todo:
            v,op,d,word = todo.pop()
            w = op(v)
            if not isinstance(w, (list, tuple)):
                w = [w]
            for w2 in w:
                self.extend(w2, d, word)
        if self._verbose is not False:
            self._bar.set_postfix({'dimension': self._stats['dimension'], 'zero': self._stats['zero']})
            self._bar.close()
            # "  dimension: %s  extensions: %s"%q(self._stats["dimension"], self._stats["extend"])


class HighestWeightSubspace(Subspace):
    def __init__(self, generators,
                 add_degrees=None,
                 degree=None,
                 hilbert_parent=None,
                 antisymmetries=None,
                 ambient=None,
                 verbose=False):
        Subspace.__init__(self, generators,
                 degree=degree,
                 add_degrees=add_degrees,
                 hilbert_parent=hilbert_parent,
                 ambient=ambient,
                 verbose=verbose)
        self._antisymmetries=antisymmetries

    @cached_method
    def finalize(self):
        R = self._ambient
        r = R._r
        assert all( not any(d[1:])
                    for d in self._bases.keys() )
        maxd = max(d[0] for d in self._bases.keys() )
        degrees = [tuple(D) for D in IntegerListsLex(max_sum=maxd, length=r, max_slope=0)]
        for D2 in degrees:
            # Apply multi polarization operators from subspaces of higher degree
            for D1 in self._bases.keys():
                D = e_polarization_degrees(D1, D2)
                if not D:
                    continue
                i, D = D
                if sum(D) == 1:
                    continue
                for p in self._bases[D1].vectors():
                    q = R.multi_polarization(p, D, i, antisymmetries=self._antisymmetries)
                    self.extend(q, D2)
            if D2 not in self._bases: # no vector of this degree was found
                continue
            # Intersect with highest weight space
            basis = self._bases[D2]
            operators = [functools.partial(R.polarization, i1=i1, i2=i2, d=1,
                                           antisymmetries=self._antisymmetries)
                         for i1 in range(1, R._r)
                         for i2 in range(i1)]
            highest_weight_space = annihilator_basis(basis._basis, operators, action=lambda b, op: op(b), ambient=R)
            self._bases[D2] = MatrixOfVectors( # Could possibly be EchelonMatrixOfVectors?
                highest_weight_space,
                ambient=R,
                )
        return "finished"

