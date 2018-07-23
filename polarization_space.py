#!/usr/bin/env python
# -*- coding: utf-8 -*-

from diagonal_polynomial_ring import *
from harmonic import *

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

def polarizationSpace(P, generators, use_symmetry=False, verbose=False):
    # use_symmetry?
    """
    Starting from  polynomials (=generators) in the mu-isotypic component of the polynomial ring in one set of variables (possibly with additional inert variables), construct the space obtained by polarization.

    P: a diagonal polynomial ring (or assymmetric version)
    generators: polynomials in one set of variables (+inert) in the image of b_mu
    """

    S = Subspace(generators=generators,operators=P.polarization_operators_by_degree(),verbose=verbose)


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

def polarization_operators_by_degree(side=None, use_symmetry=False, min_degree=0):
    pol = polarization_operators_by_multidegree(side=side,use_symmetry=use_symmetry,min_degree=min_degree)
    res = {}
    for d,op in pol.iteritems():
        if sum(d) not in res.keys():
            res[sum(d)] = op
        else:
            res[sum(d)] += op
    return res
    
    
def add_degree(d1,d2):
    d = d1 + d2
    if not all(i>=0 for i in d):
        raise ValueError("invalid degree")
    return d

# Do something with this fucntion (parameter self to remove)
def add_degree_symmetric(self,d1,d2):
    """
    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ,4,3)
        sage: D = P._grading_set
        sage: P._add_degree_symmetric(D([3,2,1]), D([-2,0,0]))
        (2, 1, 1)
        sage: P._add_degree_symmetric(D([3,2,1]), D([-2,1,4]))
        (5, 3, 1)
        sage: P._add_degree_symmetric(D([3,2,1]), D([2,1,1]))
        (5, 3, 2)
        sage: P._add_degree_symmetric(D([3,2,1]), D([2,1,-2]))
        Traceback (most recent call last):
        ...
        ValueError: invalid degree
    """
    d = d1 + d2
    if not all(i>=0 for i in d):
        raise ValueError("invalid degree")
    return self._grading_set(sorted(d, reverse=True))



@parallel()
def character_by_isotypic(P,nu,basis):
    """
        Computes the character of $Gl_r$ on the smallest submodule generated by
        the elements in `basis` indexed by `nu` and closed under the polarizators
        operators.

        INPUT:
            - `nu` -- a partition
            - `basis` -- a dict indexed by tuples of integers and partitions

        EXAMPLES::
            sage: DP = DiagonalPolynomialRingInert(QQ,3,3)
            sage: basis = DP.isotypic_basis(Partition([3]),verbose=False)
            sage: DP.character_isotypic(Partition([3]),basis)
            1
            sage: DP.character_isotypic(Partition([2,1]),basis)
            q0^2 + q0*q1 + q1^2 + q0 + q1
            sage: DP.character_isotypic(Partition([1,1,1]),basis)
            q0^3 + q0^2*q1 + q0*q1^2 + q1^3 + q0^2 + 2*q0*q1 + q1^2

    """
    if nu not in [d[1] for d in basis]:
        return 0
    else:
        nu_basis = {}
        for d,B in basis.iteritems():
            if d[1]==nu: 
                basis_nu.update({d[0]:B})
        charac = 0
        S = Subspace(generators={d:B for d,B in basis_nu.iteritems()},operators=polarization_operators_by_degree())
        for b in S.basis().values():
            charac += sum(P.multipower(P.multidegree(p),P.polynomial_ring().gens()) for p in b)
        return charac

def character_q(P,mu,parallel=False):
    """
        Computes the character and returns the result as a sum of tensor products
        of polynomials in $q$ variables for the action of $GL_r$ and Schur functions
        for the action of $S_n$.

        INPUT: `mu` a partition

        EXAMPLES::
            sage: DP.character_q(Partition([2,1]),verbose=False)
            (q0+q1)*s[1, 1, 1] + s[2, 1]
            sage: DP.character_q(Partition([3]),verbose=False)
            (q0^3+q0^2*q1+q0*q1^2+q1^3+q0^2+2*q0*q1+q1^2)*s[1, 1, 1] + (q0^2+q0*q1+q1^2+q0+q1)*s[2, 1] + s[3]
            sage: DP.character_q(Partition([1,1,1]),verbose=False)
            s[1, 1, 1]

    """
    n = P._n
    s = SymmetricFunctions(P.polynomial_ring()).s()
    charac = 0
    H = DiagonalHarmonicPolynomialsInert(P.base_ring(),P._n,P._r,inert=P._inert)
    if not isinstance(mu,Diagram):
        mu = Diagram(mu)
    if mu.size() != n:
        print "Given partition doesn't have the right size."
    else:
        basis = H.isotypic_basis(mu)
        if parallel:
            for (((nu,_),_),res) in character_by_isotypic([(P,nu,basis) for nu in Partitions(n)]):
                charac += res*s(nu)
        else:
            for nu in Partitions(n):
                charac += character_by_isotypic(P,nu,basis)*s(nu)
        return charac
