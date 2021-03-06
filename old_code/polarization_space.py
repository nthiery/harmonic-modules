#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.combinat.sf.sf import SymmetricFunctions
from sage.combinat.ranker import rank_from_list

from diagonal_polynomial_ring import *
from add_degree import *

####################################################
# Polarization Space
####################################################

#TODO use_symmetry a implementer

def polarizationSpace(P, generators, verbose=False, row_symmetry=None, use_commutativity=False, side="down"):
    """
    Starting from  polynomials (generators)of the polynomial ring in one 
    set of variables (possibly with additional inert variables), constructs
    the space obtained by polarization.
    
    The possible values for row_symmetry : 
        - "permutation" : the action of the symmetric group on the rows
        - "euler+intersection" or "decompose" or "multipolarization" for stategies on lie algebras
    
    INPUT:
    
        - `P` -- a diagonal polynomial ring (or assymmetric version)
        - `generators`: polynomials in one set of variables (and possibly inert variables) 
            
    OUTPUT: `F`  -- a Subspace

    EXAMPLES::
        sage: load("derivative_space.py")
        sage: P = DiagonalPolynomialRing(QQ, 3, 2, inert=1)
        sage: mu = Partition([3])
        sage: basis = DerivativeHarmonicSpace(QQ, mu.size()).basis_by_shape(Partition([2,1]))
        sage: generators = {}
        sage: for gen in basis : 
        ....:     d = P.multidegree((P(gen)))
        ....:     if d in generators.keys():
        ....:         generators[d] += [P(gen)]
        ....:     else:
        ....:         generators[d] = [P(gen)]
        sage: generators
        {(2, 0): [1/3*x00^2 - 2/3*x00*x01 + 2/3*x01*x02 - 1/3*x02^2],
         (1, 0): [-2*x00 + 2*x02]}
        sage: S = polarizationSpace(P, generators)
        sage: S.basis()
        {(0, 1): (x10 - x12,),
         (2, 0): (-1/2*x00^2 + x00*x01 - x01*x02 + 1/2*x02^2,),
         (1, 0): (x00 - x02,),
         (1, 1): (x00*x10 - x01*x10 - x00*x11 + x02*x11 + x01*x12 - x02*x12,),
         (0, 2): (1/2*x10^2 - x10*x11 + x11*x12 - 1/2*x12^2,)}
         
        sage: basis = DerivativeVandermondeSpaceWithInert(QQ, mu).basis_by_shape(Partition([1,1,1]))
        sage: generators = {P.multidegree(P(gen)): [P(gen) for gen in g] for (d,g) in basis.iteritems()}
        sage: generators
        {(3, 0): [-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2]}
        sage: S = polarizationSpace(P, generators)
        sage: S.basis()
        {(1, 2): (-1/2*x01*x10^2 + 1/2*x02*x10^2 - x00*x10*x11 + x01*x10*x11 + 1/2*x00*x11^2 - 1/2*x02*x11^2 + x00*x10*x12 - x02*x10*x12 - x01*x11*x12 + x02*x11*x12 - 1/2*x00*x12^2 + 1/2*x01*x12^2,),
         (3, 0): (x00^2*x01 - x00*x01^2 - x00^2*x02 + x01^2*x02 + x00*x02^2 - x01*x02^2,),
         (0, 3): (x10^2*x11 - x10*x11^2 - x10^2*x12 + x11^2*x12 + x10*x12^2 - x11*x12^2,),
         (1, 1): (-x01*x10 + x02*x10 + x00*x11 - x02*x11 - x00*x12 + x01*x12,),
         (2, 1): (-x00*x01*x10 + 1/2*x01^2*x10 + x00*x02*x10 - 1/2*x02^2*x10 - 1/2*x00^2*x11 + x00*x01*x11 - x01*x02*x11 + 1/2*x02^2*x11 + 1/2*x00^2*x12 - 1/2*x01^2*x12 - x00*x02*x12 + x01*x02*x12,)}
        
        sage: mu = Partition([2,1])
        sage: basis = DerivativeVandermondeSpaceWithInert(QQ, mu).basis_by_shape(Partition([2,1]))
        sage: generators = {P.multidegree(P(gen)): [P(gen) for gen in g] for (d,g) in basis.iteritems()}
        sage: generators
        {(0, 0): [-theta00 + theta02]}
        sage: S = polarizationSpace(P, generators)
        sage: S.basis()
        {(0, 0): (theta00 - theta02,)}

    """
    S = SymmetricFunctions(QQ)
    s = S.s()
    m = S.m()
    r = P._r
    
    if isinstance(P, DiagonalAntisymmetricPolynomialRing):
        antisymmetries = P._antisymmetries
    else:
        antisymmetries = None
        
    if row_symmetry in ("euler+intersection", "decompose", "multipolarization")  :
        # The hilbert series will be directly expressed in terms of the
        # dimensions of the highest weight spaces, thus as a symmetric
        # function in the Schur basis
        def hilbert_parent(dimensions):
            return s.sum_of_terms([Partition(d), c]
                                   for d,c in dimensions.iteritems() if c)
    elif row_symmetry == "permutation":
        def hilbert_parent(dimensions):
            return s(m.sum_of_terms([Partition(d), c]
                                     for d,c in dimensions.iteritems())
                    ).restrict_partition_lengths(r, exact=False)
    else:
        def hilbert_parent(dimensions):
            return s(S.from_polynomial(P._hilbert_parent(dimensions))
                    ).restrict_partition_lengths(r,exact=False)

    operators = polarization_operators_by_multidegree(P, side=side, row_symmetry=row_symmetry, min_degree=1 if row_symmetry and row_symmetry!="permutation" else 0)
  
    if row_symmetry == "euler+intersection":
        operators[P._grading_set.zero()] = [
            functools.partial(lambda v,i: P.polarization(P.polarization(v, i+1, i, 1, antisymmetries=antisymmetries), i, i+1, 1, antisymmetries=antisymmetries), i=i)
            for i in range(r-1)]
    elif row_symmetry == "decompose":
        def post_compose(f):
            return lambda x: [q for (q,word) in P.highest_weight_vectors_decomposition(f(x))]
        operators = {d: [post_compose(op) for op in ops]for d, ops in operators.iteritems()}
    elif row_symmetry == "multipolarization":
        F = HighestWeightSubspace(generators,
                 ambient=self,
                 add_degrees=add_degree, degree=P.multidegree,
                 hilbert_parent = hilbert_parent,
                 antisymmetries=antisymmetries,
                 verbose=verbose)
        return F
        
    operators_by_degree = {}
    for degree,ops in operators.iteritems(): 
        d = sum(degree)
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

    if row_symmetry == "permutation":
        add_deg = add_degree_symmetric
    else:
        add_deg = add_degree
    
    F = Subspace(generators, operators=operators,
                 add_degrees=add_deg, degree=P.multidegree,
                 hilbert_parent = hilbert_parent,
                 extend_word=extend_word, verbose=verbose) 
    F._antisymmetries = antisymmetries
    return F
    
        

####################################################
# Polarization Operators
####################################################
def polarization_operators_by_multidegree(P, side=None, row_symmetry=None, use_lie=False, min_degree=0):
    """
    Return the collection of polarization operators acting on harmonic polynomials,
    indexed by multi-degree.

    INPUT:

    - ``P`` -- a diagonal polynomial ring or a diagonal antisymmetric polynomial ring
    - ``side`` -- 'down'
    - ``min_degree`` -- a non negative integer `d` (default: `0`)

    If `d>0`, only return the polarization operators of differential degree `>=d`.

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
            [functools.partial(P.polarization, i1=i1, i2=i2, d=d, row_symmetry=row_symmetry)]
            for d in range(min_degree+1, n)
            for i1 in range(0, r)
            for i2 in range(0, r)
            if ((i1==i2+1 if d==1 else i1<i2) if use_lie else i1<i2 if side == 'down' else i1!=i2)
            if (i1<i2 if side == 'down' else i1!=i2)
           }

def polarization_operators_by_degree(P, side=None, row_symmetry=None, use_lie=False, min_degree=0):
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
    pol = polarization_operators_by_multidegree(P, side=side,
                                                row_symmetry=row_symmetry, 
                                                use_lie=use_lie, 
                                                min_degree=min_degree)
    res = {}
    for d,op in pol.iteritems():
        if sum(d) not in res.keys():
            res[sum(d)] = op
        else:
            res[sum(d)] += op
    return res


