#!/usr/bin/env python
# -*- coding: utf-8 -*-

from diagonal_polynomial_ring import *
from derivative_space import * #probablement inutile

"""
Potential user interface::

    sage: P = ...
    sage: generators = ...(mu, nu, ...)
    sage: space = polarizationSpace(P, generators)
    sage: space.character()  # the GL_n character

Variant::

    sage: polarization_character(P, generators)  # Qui en interne appelle polarization_space
"""

from diagonal_polynomial_ring import *


####################################################
# Polarization Space
####################################################

#TODO use_symmetry a implementer

#class PolarizationSpace():
def polarizationSpace(P, generators, use_symmetry=False, verbose=False):
    """
    Starting from  polynomials (=generators) in the mu-isotypic component of the polynomial ring in one set of variables (possibly with additional inert variables), construct the space obtained by polarization.

    P: a diagonal polynomial ring (or assymmetric version)
    generators: polynomials in one set of variables (+inert) in the image of b_mu
    """

    S = Subspace(generators=generators,operators=P.polarization_operators_by_degree(),verbose=verbose)

def harmonic_space_by_shape(P, generators, verbose=False, use_antisymmetry=False, use_symmetry=False, use_lie=False, use_commutativity=False):
        """
        Return the projection under the Young idempotent for the
        partition / tableau `mu` of the space of diagonal harmonic
        polynomials.

        This is represented as a collection of subspaces corresponding
        to the row-multidegree (aka `GL_r` weight spaces).

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,4,2)
            sage: F = P.harmonic_space_by_shape([1,1,1,1])
            sage: F.hilbert_polynomial()
            s[3, 1] + s[4, 1] + s[6]

            sage: P = DiagonalPolynomialRing(QQ,3,2)
            sage: F = P.harmonic_space_by_shape([1,1,1])
            sage: F.hilbert_polynomial()
            s[1, 1] + s[3]

            sage: P = DiagonalPolynomialRing(QQ,3,2)
            sage: F = P.harmonic_space_by_shape([1,1,1])
            sage: F.hilbert_polynomial()
            s[1, 1] + s[3]

            sage: P = DiagonalPolynomialRing(QQ,5,2)
            sage: F = P.harmonic_space_by_shape(Partition([3,2]),use_lie='multipolarization', verbose=True)
        """
        mu = Partition(mu)
        r = P._r
        S = SymmetricFunctions(ZZ)
        s = S.s()
        m = S.m()

        if use_antisymmetry: #TODO fix this : antisymmetries are given at the begin or compute in this function ?
            # FIXME: duplicated logic for computing the
            # antisymmetrization positions, here and in apply_young_idempotent
            antisymmetries = antisymmetries_of_tableau(mu.initial_tableau())
        else:
            antisymmetries = None
        if use_lie:
            # The hilbert series will be directly expressed in terms of the
            # dimensions of the highest weight spaces, thus as a symmetric
            # function in the Schur basis
            def hilbert_parent(dimensions):
                return s.sum_of_terms([Partition(d), c]
                                       for d,c in dimensions.iteritems() if c)
        elif use_symmetry:
            def hilbert_parent(dimensions):
                return s(m.sum_of_terms([Partition(d), c]
                                         for d,c in dimensions.iteritems())
                        ).restrict_partition_lengths(r, exact=False)
        else:
            def hilbert_parent(dimensions):
                return s(S.from_polynomial(self._hilbert_parent(dimensions))
                        ).restrict_partition_lengths(r,exact=False)

        ####### OPERATEURS ########
        operators = polarization_operators_by_degree(self._polRing, side='down',
                                                          use_symmetry=use_symmetry,
                                                          min_degree=1 if use_lie else 0)
        if use_lie == "euler+intersection":
            operators[self._grading_set.zero()] = [
                functools.partial(lambda v,i: self.polarization(self.polarization(v, i+1,i, 1,antisymmetries=antisymmetries), i,i+1, 1,antisymmetries=antisymmetries), i=i)
                for i in range(r-1)
                ]
        elif use_lie == 'decompose':
            def post_compose(f):
                return lambda x: [q for (q,word) in self.highest_weight_vectors_decomposition(f(x))]
            operators = {d: [post_compose(op) for op in ops]
                         for d, ops in operators.iteritems()}
        elif use_lie == 'multipolarization':
            F = HighestWeightSubspace(generators,
                     ambient=self,
                     add_degrees=self._add_degree, degree=self.multidegree,
                     hilbert_parent = hilbert_parent,
                     antisymmetries=antisymmetries,
                     verbose=verbose)
            return F

        operators_by_degree = {}
        for degree,ops in operators.iteritems():
            d = sum([degree])
            operators_by_degree.setdefault(d,[])
            operators_by_degree[d].extend(ops)
        ranks = {}
        for d, ops in operators_by_degree.iteritems():
            ranker = rank_from_list(ops)
            for op in ops:
                ranks[op] = (d, ranker(op))
        ranker = ranks.__getitem__
        def extend_word(word, op):
            new_word = word + [ranker(op)]
            if use_commutativity and sorted(new_word) != new_word:
                #print "rejected: %s"% new_word
                return None
            #print new_word
            return new_word
        # print operators
        add_degree = self.add_degree_symmetric if use_symmetry else self.add_degree
        F = Subspace(generators, operators=operators,
                     add_degrees=self.add_degree, degree=self.multidegree,
                     hilbert_parent = hilbert_parent,
                     extend_word=extend_word, verbose=verbose)
        F._antisymmetries = antisymmetries
        return F
        
        
def e(P, i):
    return functools.partial(P.polarization, i1=i, i2=i+1, d=1)

def f(P, i):
    return functools.partial(P.polarization, i1=i+1, i2=i, d=1)
    
    
def e_polarization_degrees(D1, D2):
    """
    Return the degree of an e-multipolarization operator from degree D1 to degree D2

    EXAMPLES::

        sage: e_polarization_degrees([5,0,0],[3,1,0])
        (1, [2, 0])
        sage: e_polarization_degrees([5,0,0],[3,1,0])
        (1, [2, 0])
        sage: e_polarization_degrees([5,0,0],[3,2,0])
        sage: e_polarization_degrees([5,1,0],[3,2,0])
        (1, [2, 0])
        sage: e_polarization_degrees([5,4,0,1],[1,1,0,2])
        (3, [4, 3, 0, 0])
        sage: e_polarization_degrees([5,4,0,1,0,0],[1,1,0,2,0,0])
        (3, [4, 3, 0, 0, 0, 0])
        sage: e_polarization_degrees([5,4,0,1,0,0],[1,1,0,2,0,1])
        sage: e_polarization_degrees([5,4,0,1,0,1],[1,1,0,2,0,0])


    """
    D = [D1i-D2i for D1i,D2i in zip(D1, D2)]
    for i in reversed(range(len(D))):
        if D[i] == -1:
            break
        if D[i] != 0:
            return None
    if i <= 0:
        return None
    D[i] = 0
    if any(D[j] < 0 for j in range(i)):
        return None
    return i, D



####################################################
# Polarization Operators
####################################################
def polarization_operators_by_multidegree(P, side=None, use_symmetry=False, min_degree=0):
    """
    Return the collection of polarization operators acting on harmonic polynomials

    INPUT:

    - ``P`` -- a diagonal polynomial ring or a diagonal antisymmetric polynomial ring
    - ``side`` -- 'down'
    - ``min_degree`` -- a non negative integer `d` (default: `0`)

      if `d>0`, only return the polarization operators of differential degree `>=d`.

    If ``side`` is `down` (the only implemented choice), only
    the operators from `X_{i1}` to `X_{i2}` for `i1<i2` are returned.

    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ, 4, 2)
        sage: ops = polarization_operators_by_degree(P); ops
        {(-1, 1): [<functools.partial object at ...>],
         (1, -1): [<functools.partial object at ...>],
         (-2, 1): [<functools.partial object at ...>],
         (-3, 1): [<functools.partial object at ...>],
         (1, -3): [<functools.partial object at ...>],
         (1, -2): [<functools.partial object at ...>]}

        sage: polarization_operators_by_degree(P, side="down")
        {(-3, 1): [<functools.partial object at ...>],
         (-1, 1): [<functools.partial object at ...>],
         (-2, 1): [<functools.partial object at ...>]}

        sage: P = DiagonalPolynomialRing(QQ, 3, 3)
        sage: polarization_operators_by_degree(P, side="down")
        {(-1, 1, 0): [<functools.partial object at ...>],
         (-2, 1, 0): [<functools.partial object at ...>],
         (-2, 0, 1): [<functools.partial object at ...>],
         (0, -2, 1): [<functools.partial object at ...>],
         (-1, 0, 1): [<functools.partial object at ...>],
         (0, -1, 1): [<functools.partial object at ...>]}

        sage: polarization_operators_by_degree(P, use_lie=True) # not tested (features disabled)
        {(-2, 1, 0): [<functools.partial object at ...>],
         (-2, 0, 1): [<functools.partial object at ...>],
         (0, 1, -1): [<functools.partial object at ...>],
         (0, -2, 1): [<functools.partial object at ...>],
         (1, -1, 0): [<functools.partial object at ...>]}

        sage: P = DiagonalPolynomialRing(QQ, 4, 3)
        sage: ops = polarization_operators_by_degree(P)
        sage: X = P.algebra_generators()
        sage: p = X[0,0]*X[1,0]^3*X[1,1]^1 + X[2,1]; p
        x00*x10^3*x11 + x21
        sage: ops[(1,-2,0)][0](p)
        6*x00^2*x10*x11
        sage: ops[(0,-1,1)][0](p)
        3*x00*x10^2*x11*x20 + x00*x10^3*x21
    """
    n = P._n
    r = P._r
    grading_set = P._grading_set
    return {grading_set([-d if i==i1 else 1 if i==i2 else 0 for i in range(r)]):
            [functools.partial(P.polarization, i1=i1, i2=i2, d=d, use_symmetry=use_symmetry)]
            for d in range(min_degree+1, n)
            for i1 in range(0,r)
            for i2 in range(0, r)
            #if ((i1==i2+1 if d==1 else i1<i2) if use_lie else i1<i2 if side == 'down' else i1!=i2)
            if (i1<i2 if side == 'down' else i1!=i2)
           }

def polarization_operators_by_degree(P, side=None, use_symmetry=False, min_degree=0):
    pol = polarization_operators_by_multidegree(P, side=side, use_symmetry=use_symmetry, min_degree=min_degree)
    res = {}
    for d,op in pol.iteritems():
        if sum(d) not in res.keys():
            res[sum(d)] = op
        else:
            res[sum(d)] += op
    return res



