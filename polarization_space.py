#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.combinat.sf.sf import SymmetricFunctions
from sage.combinat.ranker import rank_from_list

from diagonal_polynomial_ring import *
from add_degree import *

"""
Potential user interface::

    sage: P = ... #not tested
    sage: generators = ...(mu, nu, ...) #not tested
    sage: space = polarizationSpace(P, generators) #not tested
    sage: space.character()  # the GL_n character #not tested

Variant::

    sage: polarization_character(P, generators)  #not tested
    # Qui en interne appelle polarization_space
"""

####################################################
# Polarization Space
####################################################

#TODO use_symmetry a implementer

def polarizationSpace(P, mu, generators, verbose=False, with_inert=False, antisymmetries=None, use_symmetry=False, use_lie=False, use_commutativity=False):
    """
    Starting from  polynomials (=generators) in the mu-isotypic component 
    of the polynomial ring in one set of variables (possibly with 
    additional inert variables), construct the space obtained by polarization.
    
    INPUT:
    
        - `P` -- a diagonal polynomial ring (or assymmetric version)
        - `mu` -- a partition corresponding to the isotypic component `b_mu`
        - `generators`: polynomials in one set of variables 
            (and possibly inert varaibles) in the image of `b_mu`  
            
    OUTPUT: `F`  -- a Subspace
    
    FIXME: duplicated logic for computing the
    antisymmetrization positions, given here and computing in apply_young_idempotent

    EXAMPLES::
        sage: load("derivative_space.py")
        sage: P = DiagonalPolynomialRing(QQ, 3, 2, inert=1)
        sage: mu = Partition([3])
        sage: generators = DerivativeVandermondeSpaceWithInert(QQ, mu).basis_by_shape(Partition([2,1]))
        sage: generators
        {(1, [2, 1]): [x00 - x02],
         (2, [2, 1]): [x00^2 - 2*x00*x01 + 2*x01*x02 - x02^2]}
        sage: S = polarizationSpace(P, mu, generators, with_inert=True)
        sage: S.basis()
        {(1, [2, 1]): (x00 - x02, x10 - x12),
         (2, [2, 1]): (-1/2*x00^2 + x00*x01 - x01*x02 + 1/2*x02^2,
          x00*x10 - x01*x10 - x00*x11 + x02*x11 + x01*x12 - x02*x12,
          1/2*x10^2 - x10*x11 + x11*x12 - 1/2*x12^2)}
        sage: generators = DerivativeVandermondeSpaceWithInert(QQ, mu).basis_by_shape(Partition([1,1,1]))
        sage: generators
        {(3,
          [1, 1, 1]): [-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2]}
        sage: S = polarizationSpace(P, mu, generators, with_inert=True)
        sage: S.basis()
        {(2, [1, 1, 1]): (-x01*x10 + x02*x10 + x00*x11 - x02*x11 - x00*x12 + x01*x12,),
         (3,
          [1, 1, 1]): (x00^2*x01 - x00*x01^2 - x00^2*x02 + x01^2*x02 + x00*x02^2 - x01*x02^2, -x00*x01*x10 + 1/2*x01^2*x10 + x00*x02*x10 - 1/2*x02^2*x10 - 1/2*x00^2*x11 + x00*x01*x11 - x01*x02*x11 + 1/2*x02^2*x11 + 1/2*x00^2*x12 - 1/2*x01^2*x12 - x00*x02*x12 + x01*x02*x12, -1/2*x01*x10^2 + 1/2*x02*x10^2 - x00*x10*x11 + x01*x10*x11 + 1/2*x00*x11^2 - 1/2*x02*x11^2 + x00*x10*x12 - x02*x10*x12 - x01*x11*x12 + x02*x11*x12 - 1/2*x00*x12^2 + 1/2*x01*x12^2, x10^2*x11 - x10*x11^2 - x10^2*x12 + x11^2*x12 + x10*x12^2 - x11*x12^2)}

        sage: mu = Partition([2,1])
        sage: generators = DerivativeVandermondeSpaceWithInert(QQ, mu).basis_by_shape(Partition([2,1]))
        sage: generators
        {(0, [2, 1]): [-theta00 + theta02]}
        sage: S = polarizationSpace(P, mu, generators, with_inert=True)
        sage: S.basis()
        {(0, [2, 1]): (theta00 - theta02,)}
        
    TODO:: add exemples for harmonics with no inert variables
           there may be some bugs to correct

    """
    # FIXME mu is useless for now, usefull only if antisymmetries computed here
    mu = Partition(mu)
    r = P._r
    S = SymmetricFunctions(ZZ)
    s = S.s()
    m = S.m()
    
    # Change of ring (one set on variables to multisets of variables)
    # To be able to use polarization
    if isinstance(generators, dict):
        new_generators = {d:[P(gen) for gen in g] for (d,g) in generators.iteritems()}
    else:
        return "generators should be a dictonnary."
        
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
    elif with_inert:
        def hilbert_parent(dimensions):
            return s.sum_of_terms([Partition(d), c] for c,d in dimensions.iterkeys())
    else:
        def hilbert_parent(dimensions):
            return s(S.from_polynomial(P._hilbert_parent(dimensions))
                    ).restrict_partition_lengths(r,exact=False)

    if with_inert:
        operators_by_degree = polarization_operators_by_degree(P, use_symmetry=use_symmetry)
    else:
        operators = polarization_operators_by_multidegree(P, side='down',
                                                          use_symmetry=use_symmetry,
                                                          min_degree=1 if use_lie else 0)
        if use_lie == "euler+intersection":
            operators[P._grading_set.zero()] = [
                functools.partial(lambda v,i: P.polarization(P.polarization(v, i+1, i, 1, antisymmetries=antisymmetries), i, i+1, 1, antisymmetries=antisymmetries), i=i)
                for i in range(r-1)
                ]
        elif use_lie == 'decompose':
            def post_compose(f):
                return lambda x: [q for (q,word) in P.highest_weight_vectors_decomposition(f(x))]
            operators = {d: [post_compose(op) for op in ops]
                         for d, ops in operators.iteritems()}
        elif use_lie == 'multipolarization':
            F = HighestWeightSubspace(generators,
                     ambient=self,
                     add_degrees=add_degree, degree=P.multidegree,
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
            return None
        return new_word
    if use_symmetry:
        add_degree = add_degree_symmetric
    elif with_inert:
        add_degree = add_degree_polarization
    else:
        add_degree = add_degree
        
    F = Subspace(new_generators, operators=operators_by_degree,
                 add_degrees=add_degree, degree=P.multidegree,
                 hilbert_parent = hilbert_parent,
                 extend_word=extend_word, verbose=verbose) 
    F._antisymmetries = antisymmetries
    return F
    
        

####################################################
# Polarization Operators
####################################################
def polarization_operators_by_multidegree(P, side=None, use_symmetry=False, min_degree=0):
    """
    Return the collection of polarization operators acting on harmonic polynomials,
    indexed by multi-degree.

    INPUT:

    - ``P`` -- a diagonal polynomial ring or a diagonal antisymmetric polynomial ring
    - ``side`` -- 'down'
    - ``min_degree`` -- a non negative integer `d` (default: `0`)

      if `d>0`, only return the polarization operators of differential degree `>=d`.

    If ``side`` is `down` (the only implemented choice), only
    the operators from `X_{i1}` to `X_{i2}` for `i1<i2` are returned.

    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ, 4, 2)
        sage: ops = polarization_operators_by_multidegree(P); ops
        {(-1, 1): [<functools.partial object at ...>],
         (1, -1): [<functools.partial object at ...>],
         (-2, 1): [<functools.partial object at ...>],
         (-3, 1): [<functools.partial object at ...>],
         (1, -3): [<functools.partial object at ...>],
         (1, -2): [<functools.partial object at ...>]}

        sage: polarization_operators_by_multidegree(P, side="down")
        {(-3, 1): [<functools.partial object at ...>],
         (-1, 1): [<functools.partial object at ...>],
         (-2, 1): [<functools.partial object at ...>]}

        sage: P = DiagonalPolynomialRing(QQ, 3, 3)
        sage: polarization_operators_by_multidegree(P, side="down")
        {(-1, 1, 0): [<functools.partial object at ...>],
         (-2, 1, 0): [<functools.partial object at ...>],
         (-2, 0, 1): [<functools.partial object at ...>],
         (0, -2, 1): [<functools.partial object at ...>],
         (-1, 0, 1): [<functools.partial object at ...>],
         (0, -1, 1): [<functools.partial object at ...>]}

        sage: polarization_operators_by_multidegree(P, use_lie=True) # not tested (features disabled)
        {(-2, 1, 0): [<functools.partial object at ...>],
         (-2, 0, 1): [<functools.partial object at ...>],
         (0, 1, -1): [<functools.partial object at ...>],
         (0, -2, 1): [<functools.partial object at ...>],
         (1, -1, 0): [<functools.partial object at ...>]}

        sage: P = DiagonalPolynomialRing(QQ, 4, 3)
        sage: ops = polarization_operators_by_multidegree(P)
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
    """
    Return the collection of polarization operators acting on harmonic polynomials,
    indexed by multi-degree.
    
    INPUT:

    - ``P`` -- a diagonal polynomial ring or a diagonal antisymmetric polynomial ring
    - ``side`` -- 'down'
    - ``min_degree`` -- a non negative integer `d` (default: `0`)
    
    If ``side`` is `down` (the only implemented choice), only
    the operators from `X_{i1}` to `X_{i2}` for `i1<i2` are returned.
    
    EXAMPLES::
        sage: P = DiagonalPolynomialRing(QQ, 4, 2)
        sage: ops = polarization_operators_by_degree(P); ops
        {-2: [<functools.partial object at ...>,
          <functools.partial object at ...>],
         -1: [<functools.partial object at ...>,
          <functools.partial object at ...>],
         0: [<functools.partial object at ...>,
          <functools.partial object at ...>]}
        sage: polarization_operators_by_degree(P, side="down")
        {-2: [<functools.partial object at ...>],
         -1: [<functools.partial object at ...>],
         0: [<functools.partial object at ...>]}

    """
    pol = polarization_operators_by_multidegree(P, side=side, use_symmetry=use_symmetry, min_degree=min_degree)
    res = {}
    for d,op in pol.iteritems():
        if sum(d) not in res.keys():
            res[sum(d)] = op
        else:
            res[sum(d)] += op
    return res


