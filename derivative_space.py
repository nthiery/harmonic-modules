#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.parallel.decorate import parallel
from sage.combinat.ranker import rank_from_list

from utilities import index_filling
from antisymmetric_utilities import *
from diagonal_polynomial_ring import *
from polynomial_derivative import *


####################################################
# Derivative Harmonic Space
####################################################

class DerivativeHarmonicSpace():
    """

        The space generated by the Vandermonde determinant and
        its derivatives.

        EXAMPLES::

            sage: P = DerivativeHarmonicSpace(QQ, 4, 3)
            sage:
    """
    def __init__(self, R, n, antisymmetries=None):
        self._R = R
        self._n = n
        self._antisymmetries = antisymmetries
        if antisymmetries: 
            self._polRing = DiagonalAntisymmetricPolynomialRing(R, n, 1, antisymmetries)
        else:
            self._polRing = DiagonalPolynomialRing(R, n, 1)
            
    def _repr_(self):
        """
            sage:

        """
        return "Derivative space generated by the Vandermonde determinant of degree %s and its derivatives"%(self._n)

    def add_degree(self,d1,d2):
        d = d1 + d2
        if not all(i>=0 for i in d):
            raise ValueError("invalid degree")
        return d

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
        return self._polRing._grading_set(sorted(d, reverse=True))
        
    def basis_by_shape(self, mu): 
        mu = Partition(mu)
        if self._antisymmetries:
            use_antisymmetry = True
        else:
            use_antisymmetry = False
        return [self.higher_specht(t, harmonic=True, use_antisymmetry=use_antisymmetry)
                      for t in StandardTableaux(mu)]

    def is_highest_weight_vector(self, p, _assert=False):
        for i2 in range(self._r):
            for i1 in range(i2):
                if self.polarization(p, i2, i1, 1):
                    if _assert:
                        assert False
                    else:
                        return False
        return True

    def test_highest_weight_vector(self, p):
        self.is_highest_weight_vector(p, _assert=True)

    def highest_weight_vectors(self, p, i1=None, i2=None):
        """
        Return the "unique" highest weight vectors `p_j, j\geq 0` such
        that `p = \sum e^j p_j`.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 4, 2)
            sage: X = P.algebra_generators()
            sage: P.highest_weight_vectors(X[0,0], 0, 1)
            [x00]
            sage: P.highest_weight_vectors(X[0,0], 1, 0)
            [0, x10]

            sage: P.highest_weight_vectors(X[1,0]^3, 0, 1)
            [0, 0, 0, 1/6*x00^3]
            sage: P.test_highest_weight_vectors(X[1,0]^3, 0, 1)

            sage: P.highest_weight_vectors(p, 0, 1)  # not tested
            [-x01*x10 + x00*x11, x00^2 - x01^2]
            sage: P.test_highest_weight_vectors(p, 0, 1)   # not tested

        A random example::

            sage: P = DiagonalPolynomialRing(QQ, 4, 3)
            sage: P.inject_variables()
            Defining x00, x01, x02, x03, x10, x11, x12, x13, x20, x21, x22, x23
            sage: x00, x01, x02, x03, x10, x11, x12, x13, x20, x21, x22, x23 = P._P.gens()
            sage: p = 1/2*x10^2*x11*x20 + 3*x10*x11*x12*x20 + 1/3*x11^2*x12*x20 + 1/2*x10*x11*x12*x21 + x10*x11^2*x22 + 1/15*x10*x11*x12*x22 - 2*x11^2*x12*x22 - 2*x12^3*x22
            sage: res = P.highest_weight_vectors(p); res
            [1/48*x00^2*x01*x10 + 1/4*x00*x01*x02*x10 - 1/48*x01^2*x02*x10 - 1/360*x01*x02^2*x10 - 1/48*x00^3*x11 - 1/8*x00^2*x02*x11 - 5/72*x00*x01*x02*x11 - 1/360*x00*x02^2*x11 + 1/6*x01*x02^2*x11 - 1/8*x00^2*x01*x12 + 13/144*x00*x01^2*x12 + 1/180*x00*x01*x02*x12 - 1/6*x01^2*x02*x12,
            1/48*x00^3*x01 + 1/8*x00^2*x01*x02 + 11/144*x00*x01^2*x02 + 1/360*x00*x01*x02^2 - 1/12*x01^2*x02^2 - 1/12*x02^4]
            sage: [P.multidegree(q) for q in res]
            [(3, 1, 0), (4, 0, 0)]
            sage: for q in res:
            ....:     P.test_highest_weight_vector(q)

        .. TODO:: Check that p is indeed in the span of res

        Failing for the strategy of clearing HW for i1,i2 in increasing revlex  order:

            sage: p = 11*x01*x12*x20*x21^2 + 1/3*x00*x12*x20^2*x22 - 1/8*x02*x11*x20*x22^2


        Failing for the strategy of taking the reduced word 1,0,1, or any repeat thereof:

            sage: p = 891/2097152*x01^3*x02*x10 + 27/1048576*x00^2*x02^2*x10 - 81/16777216*x01*x02^3*x10 + 891/1048576*x00*x01^2*x02*x11 + 243/16777216*x00*x02^3*x11 - 2673/2097152*x00*x01^3*x12 - 27/1048576*x00^3*x02*x12 - 81/8388608*x00*x01*x02^2*x12
        """
        # Define HW_{i1,i2}(q) as the predicate
        #   q highest weight for i1, i2; namely: e_{i1,i2}.q = 0
        # Define HW_{<i1,i2}(q) as the predicate
        #   HW_{i1',i2'}(q) for i1'<i2' with (i1',i2') <_{revlex} (i1,i2)
        # Define similarly HW_{≤i1,i2}(q)
        if i1 is None and i2 is None:
            ps = [p]
            # HR:
            # - p is in the span of ps upon application of e_i,j operators
            # - for any q in ps, HW_{<i1,i2}(q)
            for zut in range(5):
                for i2 in range(self._r-1):
                    for i1 in range(self._r-2,i2-1,-1):
                        ps = [r
                                  for q in ps
                                  for r in self.highest_weight_vectors(q, i1, i1+1)
                                  if r]
            return ps

        # Precondition: HW_{<i1,i2}(p)
        # Goal: produce pjs such that:
        # - p = \sum_j e^j pjs[j]
        # - HW_{≤ i1, i2}(q) for q in pjs
        e = functools.partial(self.polarization, i1=i1, i2=i2, d=1)
        f = functools.partial(self.polarization, i1=i2, i2=i1, d=1)
        D = self.multidegree(p)
        w = D[i1] - D[i2]

        # Invariant: fis[i]: f^i(p)
        fip = p
        fis = []
        while fip:
            fis.append(fip)
            fip = f(fip)

        # Invariants:
        # pjs[j]: None or p_j
        # pijs[j]: None or e^(j-i) p_j
        pjs = [ None for j in range(len(fis)) ]
        epjs = [ None for j in range(len(fis)) ]
        for i in range(len(fis)-1, -1, -1):
            for j in range(i+1, len(pjs)):
                epjs[j] = e(epjs[j])
            r = fis[i] - sum(fiej(i,j,w+2*j) * epjs[j] for j in range(i+1, len(epjs)))
            if r:
                pjs[i] = r / fiej(i,i,w+2*i)
            else:
                pjs[i] = r
            epjs[i] = pjs[i]
        # for i2p in range(i2+1):
        #     for i1p in range(i2p):
        #         for q in pjs:
        #             assert self.polarization(q, i2p, i1p, d=1) == 0
        return pjs

    def test_highest_weight_vectors(self, p, i1, i2):
        e = functools.partial(self.polarization, i1=i1, i2=i2, d=1)
        f = functools.partial(self.polarization, i1=i2, i2=i1, d=1)
        pjs = list(self.highest_weight_vectors(p, i1, i2))
        for q in pjs:
            assert f(q) == 0
        for j in range(len(pjs)):
            for i in range(j):
                pjs[j] = e(pjs[j])
        assert p == sum(pjs)

    def strip_highest_weight_vector(self, p):
        """
        EXAMPLES::

            sage: R = DiagonalPolynomialRing(QQ, 3, 3)
            sage: R.inject_variables()
            Defining x00, x01, x02, x10, x11, x12, x20, x21, x22
            sage: x00, x01, x02, x10, x11, x12, x20, x21, x22 = R._P.gens()
            sage: R.strip_highest_weight_vector(x00)
            (x00, [], 0)
            sage: R.strip_highest_weight_vector(x20)
            (x00, [[1, 1], [0, 1]], 0)
            sage: R.strip_highest_weight_vector(x20^2)
            (4*x00^2, [[1, 2], [0, 2]], 0)
        """
        W = SymmetricGroup(range(self._r))
        w0 = W.long_element().reduced_word()
        word = []
        q = p
        for i in w0:
            l = 0
            while True:
                q2 = self.polarization(q, i+1, i, 1)
                if q2:
                    q = q2
                    l += 1
                else:
                    break
            if l:
                word.append([i,l])
        q2 = q
        for i,l in reversed(word):
            D = self.multidegree(q2)
            w = D[i] - D[i+1]
            for l2 in range(l):
                q2 = self.polarization(q2, i, i+1, 1)
            q2 /= fiej(l, l, w)
        self.test_highest_weight_vector(q)
        return q, word, p-q2

    def highest_weight_vectors_decomposition(self, p):
        """
        EXAMPLES::

            sage: R = DiagonalPolynomialRing(QQ, 3, 3)
            sage: R.inject_variables()
            Defining x00, x01, x02, x10, x11, x12, x20, x21, x22
            sage: x00, x01, x02, x10, x11, x12, x20, x21, x22 = R._P.gens()
            sage: e0 = R.e(0); e1 = R.e(1)
            sage: p = e1(e0(e0(3*x00^3))) + e0(e1(e0(x01*x02^2)))
            sage: R.highest_weight_vectors_decomposition(p)
            [[36*x00^3 + 6*x01*x02^2, [[0, 1], [1, 1], [0, 1]]]]

            sage: p = 1/2*x10^2*x11*x20 + 3*x10*x11*x12*x20 + 1/3*x11^2*x12*x20 + 1/2*x10*x11*x12*x21 + x10*x11^2*x22 + 1/15*x10*x11*x12*x22 - 2*x11^2*x12*x22 - 2*x12^3*x22
            sage: R.highest_weight_vectors_decomposition(p)
            [[3*x00^3*x01 + 18*x00^2*x01*x02 + 11*x00*x01^2*x02 + 2/5*x00*x01*x02^2 - 12*x01^2*x02^2 - 12*x02^4,
            [[0, 3], [1, 1], [0, 1]]],
            [3/4*x00^2*x01*x10 + 9*x00*x01*x02*x10 - 3/4*x01^2*x02*x10 - 1/10*x01*x02^2*x10 - 3/4*x00^3*x11 - 9/2*x00^2*x02*x11 - 5/2*x00*x01*x02*x11 - 1/10*x00*x02^2*x11 + 6*x01*x02^2*x11 - 9/2*x00^2*x01*x12 + 13/4*x00*x01^2*x12 + 1/5*x00*x01*x02*x12 - 6*x01^2*x02*x12,
            [[0, 3], [1, 1]]]]

        On a non trivial highest weight vector::

            sage: f0 = R.f(0)
            sage: f1 = R.f(1)
            sage: p = 891/2097152*x01^3*x02*x10 + 27/1048576*x00^2*x02^2*x10 - 81/16777216*x01*x02^3*x10 + 891/1048576*x00*x01^2*x02*x11 + 243/16777216*x00*x02^3*x11 - 2673/2097152*x00*x01^3*x12 - 27/1048576*x00^3*x02*x12 - 81/8388608*x00*x01*x02^2*x12
            sage: f0(p)
            0
            sage: f1(p)
            0
            sage: R.multidegree(p)
            (4, 1, 0)
            sage: R.highest_weight_vectors_decomposition(p) == [[p, []]]
            True

        Found while computing harmonic::

            sage: R = DiagonalPolynomialRing(QQ, 4, 3)
            sage: R.inject_variables()
            Defining x00, x01, x02, x10, x11, x12, x20, x21, x22
            sage: p = 1/2*x02*x10*x20 - 1/2*x03*x10*x20 - 5/2*x02*x11*x20 + 5/2*x03*x11*x20 - 3/2*x00*x12*x20 - 1/2*x01*x12*x20 + 2*x02*x12*x20 + 3/2*x00*x13*x20 + 1/2*x01*x13*x20 - 2*x03*x13*x20 - 2*x02*x10*x21 + 2*x03*x10*x21 + 2*x00*x12*x21 - 2*x03*x12*x21 - 2*x00*x13*x21 + 2*x02*x13*x21 - 2*x00*x10*x22 + 1/2*x01*x10*x22 + 3/2*x02*x10*x22 + 5/2*x00*x11*x22 - 5/2*x03*x11*x22 - 1/2*x00*x12*x22 + 1/2*x03*x12*x22 - 1/2*x01*x13*x22 - 3/2*x02*x13*x22 + 2*x03*x13*x22 + 2*x00*x10*x23 - 1/2*x01*x10*x23 - 3/2*x03*x10*x23 - 5/2*x00*x11*x23 + 5/2*x02*x11*x23 + 1/2*x01*x12*x23 - 2*x02*x12*x23 + 3/2*x03*x12*x23 + 1/2*x00*x13*x23 - 1/2*x02*x13*x23

            sage: p = x02*x10*x20 - x00*x12*x20
            sage: R.multidegree(p)
            (1, 1, 1)

            sage: q
            x00*x02*x10 - x00^2*x12
            sage: e0(e1(q))
            x02*x10*x20 + x00*x12*x20 - 2*x00*x10*x22
            sage: e1(e0(q))
            2*x02*x10*x20 - x00*x12*x20 - x00*x10*x22


        """
        result = []
        while p:
            q, word, p = self.strip_highest_weight_vector(p)
            result.append([q, word])
        return result

    def higher_specht(self, P, Q=None, harmonic=False, use_antisymmetry=False):
        r"""
        Return the hyper specht polynomial indexed by `P` and `Q` in the first row of variables

        See :func:`higher_specht` for details.

        EXAMPLES::

            sage: R = DiagonalPolynomialRing(QQ, 3, 2)
            sage: R.algebra_generators()
            [x00 x01 x02]
            [x10 x11 x12]

            sage: for la in Partitions(3):
            ....:     for P in StandardTableaux(la):
            ....:         print ascii_art(la, R.higher_specht(P), sep="    ")
            ....:         print
            ....:
            ***    6
            <BLANKLINE>
            *
            **    -x00*x01 + x01*x02
            <BLANKLINE>
            *
            **    -2*x00 + 2*x02
            <BLANKLINE>
            *
            *
            *    -x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2

            sage: for la in Partitions(3):
            ....:     for P in StandardTableaux(la):
            ....:         print ascii_art(la, R.higher_specht(P, use_antisymmetry=True), sep="    ")
            ....:         print
            ....:
            ***    6
            <BLANKLINE>
            *
            **    -x00*x01
            <BLANKLINE>
            *
            **    -2*x00
            <BLANKLINE>
            *
            *
            *    -x00^2*x01
        """
        X = self._polRing.algebra_generators()
        # the self._n forces a multivariate polynomial ring even if n=1
        R = PolynomialRing(self._polRing.base_ring(), self._n, list(X[0]))
        H = higher_specht(R, P, Q, harmonic=harmonic, use_antisymmetry=use_antisymmetry)
        #return self(H)
        return H

    
    
###########################
# Higher Specht
###########################
        
@cached_function
def higher_specht(R, P, Q=None, harmonic=False, use_antisymmetry=False):
    """
    Return a basis element of the coinvariants

    INPUT:

    - `R` -- a polynomial ring
    - `P` -- a standard tableau of some shape `\lambda`, or a partition `\lambda`
    - `Q` -- a standard tableau of shape `\lambda`
             (default: the initial tableau of shape `\lambda`)

    - ``harmonic`` -- a boolean (default False)

    The family `(H_{P,Q})_{P,Q}` is a basis of the space of `R_{S_n}`
    coinvariants in `R` which is compatible with the action of the
    symmetric group: namely, for each `P`, the family `(H_{P,Q})_Q`
    forms the basis of an `S_n`-irreducible module `V_{P}` of type
    `\lambda`.

    If `P` is a partition `\lambda` or equivalently the initial
    tableau of shape `\lambda`, then `H_{P,Q}` is the usual Specht
    polynomial, and `V_P` the Specht module.

    EXAMPLES::

        sage: Tableaux.options.convention="french"

        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         for Q in StandardTableaux(la):
        ....:             print ascii_art(la, P, Q, factor(higher_specht(R, P, Q)), sep="    ")
        ....:             print
        ***      1  2  3      1  2  3    2 * 3
        <BLANKLINE>
        *       2         2
        **      1  3      1  3    (-1) * z * (x - y)
        <BLANKLINE>
        *       2         3
        **      1  3      1  2    (-1) * y * (x - z)
        <BLANKLINE>
        *       3         2
        **      1  2      1  3    (-2) * (x - y)
        <BLANKLINE>
        *       3         3
        **      1  2      1  2    (-2) * (x - z)
        <BLANKLINE>
        *      3      3
        *      2      2
        *      1      1    (y - z) * (-x + y) * (x - z)

        sage: factor(higher_specht(R, Partition([2,1])))
        (-2) * (x - z)

        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         print ascii_art(la, P, factor(higher_specht(R, P)), sep="    ")
        ....:         print
        ***      1  2  3    2 * 3
        <BLANKLINE>
        *       2
        **      1  3    (-1) * y * (x - z)
        <BLANKLINE>
        *       3
        **      1  2    (-2) * (x - z)
        <BLANKLINE>
        *      3
        *      2
        *      1    (y - z) * (-x + y) * (x - z)

        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         for Q in StandardTableaux(la):
        ....:             print ascii_art(la, P, Q, factor(higher_specht(R, P, Q, harmonic=True)), sep="    ")
        ....:             print
        ***      1  2  3      1  2  3    2 * 3
        <BLANKLINE>
        *       2         2
        **      1  3      1  3    (-1/3) * (-x - y + 2*z) * (x - y)
        <BLANKLINE>
        *       2         3
        **      1  3      1  2    (-1/3) * (-x + 2*y - z) * (x - z)
        <BLANKLINE>
        *       3         2
        **      1  2      1  3    (-2) * (x - y)
        <BLANKLINE>
        *       3         3
        **      1  2      1  2    (-2) * (x - z)
        <BLANKLINE>
        *      3      3
        *      2      2
        *      1      1    (y - z) * (-x + y) * (x - z)
        <BLANKLINE>

        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         for Q in StandardTableaux(la):
        ....:             print ascii_art(la, P, Q, factor(higher_specht(R, P, Q, harmonic="dual")), sep="    ")
        ....:             print
        ***      1  2  3      1  2  3    2^2 * 3
        <BLANKLINE>
        *       2         2
        **      1  3      1  3    (-2) * (-x^2 - 2*x*y + 2*y^2 + 4*x*z - 2*y*z - z^2)
        <BLANKLINE>
        *       2         3
        **      1  3      1  2    (-2) * (x^2 - 4*x*y + y^2 + 2*x*z + 2*y*z - 2*z^2)
        <BLANKLINE>
        *       3         2
        **      1  2      1  3    (-2) * (-x + 2*y - z)
        <BLANKLINE>
        *       3         3
        **      1  2      1  2    (-2) * (x + y - 2*z)
        <BLANKLINE>
        *      3      3
        *      2      2
        *      1      1    (6) * (y - z) * (-x + y) * (x - z)
        <BLANKLINE>

    This caught two bugs::

        sage: R = DiagonalPolynomialRing(QQ, 6, 1)
        sage: for mu in Partitions(6):             # long time
        ....:     for t in StandardTableaux(mu):
        ....:         p = R.higher_specht(t, harmonic=True, use_antisymmetry=True)
    """
    if not isinstance(P, StandardTableau):
        P = Partition(P).initial_tableau()
    n = P.size()
    assert (n == R.ngens()),"Given partition doesn't have the right size."
    if Q is None:
        Q = P.shape().initial_tableau()
    if harmonic == "dual":
        # Computes an harmonic polynomial obtained by applying h as
        # differential operator on the van der mond
        P = P.conjugate()
        Q = Q.conjugate() # Is this really what we want?
        h = higher_specht(R, P, Q)
        vdm = higher_specht(R, Partition([1]*n).initial_tableau())
        return polynomial_derivative(h, vdm)
    elif harmonic:
        # TODO: normalization
        n = R.ngens()
        Sym = SymmetricFunctions(R.base_ring())
        m = Sym.m()
        p = Sym.p()
        d = P.cocharge()
        B = [higher_specht(R, P, Q, use_antisymmetry=use_antisymmetry)] + \
            [higher_specht(R, P2, Q, use_antisymmetry=use_antisymmetry) * m[nu].expand(n, R.gens())
             for P2 in StandardTableaux(P.shape()) if P2.cocharge() < d
             for nu in Partitions(d-P2.cocharge(), max_length=n)]
        if use_antisymmetry:
            antisymmetries = antisymmetries_of_tableau(Q)
            B = [antisymmetric_normal(b, n, 1, antisymmetries) for b in B]
        operators = [p[k].expand(n,R.gens()) for k in range(1,n+1)]
        if use_antisymmetry:
            def action(e, f):
                return antisymmetric_normal(polynomial_derivative(e,f), n, 1, antisymmetries)
        else:
            action = polynomial_derivative
        ann = annihilator_basis(B, operators, action=action, side='left')
        assert len(ann) == 1
        return ann[0]

    exponents = index_filling(P)
    X = R.gens()
    m = R.prod(X[i-1]**d for (d,i) in zip(exponents.entries(), Q.entries()))
    return apply_young_idempotent(m, Q, use_antisymmetry=use_antisymmetry)



#########################################################
# Derivative Vandermonde Space with Inert Variables
#########################################################


class DerivativeVandermondeSpaceWithInert():
    """

        The space generated by a generalized version of the Vandermonde determinant 
        containing inert variables with respect to the derivation and its derivatives.
        
        EXAMPLES::

            sage: 
    """

    def __init__(self, R, mu, inert=1, use_antisymmetry=True):
        self._R = R
        self._mu = Partition(mu)
        self._n = Partition(mu).size()
        self._inert = inert
        self._use_antisymmetry = use_antisymmetry
        self._polRing = DiagonalPolynomialRing(R, self._n, 1, inert)
            
    def _repr_(self):
        """

        """
        return "Derivative space generated by a generalized version of the Vandermonde determinant of degree %s with inert variables and its derivatives"%(self._n)

    def vandermonde(self):
        """
            Let `mu` be a diagram (of a partition or no) and $X=(x_i)$ and
            $\Theta = (\theta_i)$ two sets of n variables.
            Then $\Delta$ is the determinant of the matrix $(x_i^a\theta_i^b)$
            for (a,b) the cells of `mu`.

            INPUT: A partition `mu`

            OUTPUT: The determinant Delta

            EXAMPLES::
                sage: S = DerivativeVandermondeSpaceWithInert(QQ,[3])
                sage: S.vandermonde()
                -x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2
                sage: S = DerivativeVandermondeSpaceWithInert(QQ,[2,1])
                sage: S.vandermonde()
                -x01*x10 + x02*x10 + x00*x11 - x02*x11 - x00*x12 + x01*x12
                sage: S = DerivativeVandermondeSpaceWithInert(QQ,[1,1,1])
                sage: S.vandermonde()
                -x10^2*x11 + x10*x11^2 + x10^2*x12 - x11^2*x12 - x10*x12^2 + x11*x12^2


        """
        n = self._n
        mu = self._mu
        X = self._polRing.variables()
        Theta = self._polRing.inert_variables()
        if not isinstance(mu,Diagram):
            mu = Diagram(mu)
        Delta = matrix([[x**i[1]*theta**i[0] for i in mu.cells()] for x,theta in zip(X[0],Theta[0])]).determinant()
        return Delta

    def dimension_vandermonde(self):
        return sum([i[1] for i in self._mu.cells()])
    
    def add_degree_isotyp(self,d1,d2):
        """
            INPUT:
                - ``d1``,``d2`` -- lists containing an integer and a partition

            OUTPUT:
                a list containing the sum of the integers of
                `d1` and `d2` and the partition contained in `d2`

            EXAMPLES::
                sage: d1 = (3,[2,1])
                sage: d2 = (-1,[3])
                sage: DP.add_degree_isotyp(d1,d2)
                (2, [3])

        """
        
        return d1[0]+d2[0], d2[1]
        
    @cached_method
    def basis_by_shape(self, verbose=False):
        """
            Let $W$ be the smallest submodule generated by a Vandermonde $\Delta$ depending on
            a partition`mu` and closed under partial derivatives.
            Then $W$ can be decomposed into isotypic components for the action of $S_n$. This function
            compute the basis of W using the Young idempotents to project on isotypic components.

            EXAMPLES::
                sage: S = DerivativeVandermondeSpaceWithInert(QQ,[3])
                sage: S.basis_by_shape()
                {(0, [3]): [1],
                 (1, [2, 1]): [x00],
                 (2, [2, 1]): [x00^2 - 2*x00*x01],
                 (3, [1, 1, 1]): [-x00^2*x01]}
                sage: S = DerivativeVandermondeSpaceWithInert(QQ,[2,1])
                sage: S.basis_by_shape()
                {(0, [2, 1]): [-x10 + x12], (1, [1, 1, 1]): [-x00*x11 + x00*x12]}
                sage: S = DerivativeVandermondeSpaceWithInert(QQ,[1,1,1])
                sage: S.basis_by_shape()
                {(0,
                  [1, 1, 1]): [-x10^2*x11 + x10*x11^2 + x10^2*x12 - x11^2*x12 - x10*x12^2 + x11*x12^2]}
                sage: S = DerivativeVandermondeSpaceWithInert(QQ,[1,1,1],use_antisymmetry=False)
                sage: S.basis_by_shape()
                {(0,
                  [1, 1, 1]): (-x10^2*x11 + x10*x11^2 + x10^2*x12 - x11^2*x12 - x10*x12^2 + x11*x12^2,)}
                sage: S = DerivativeVandermondeSpaceWithInert(QQ,[2,1],use_antisymmetry=False)
                sage: S.basis_by_shape()
                {(0, [2, 1]): (-x10 + x12,),
                 (1, [1, 1, 1]): (x01*x10 - x02*x10 - x00*x11 + x02*x11 + x00*x12 - x01*x12,)}
                sage: S = DerivativeVandermondeSpaceWithInert(QQ,[3],use_antisymmetry=False)
                sage: S.basis_by_shape()
                {(0, [3]): (1,),
                 (1, [2, 1]): (x00 - x02,),
                 (2, [2, 1]): (x00^2 - 2*x00*x01 + 2*x01*x02 - x02^2,),
                 (3,
                  [1, 1, 1]): (-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2,)}

        """
        n = self._n
        mu = self._mu
        X = self._polRing.variables()
        Delta = self.vandermonde()
        dim = self.dimension_vandermonde()
        operators = {}
        for nu in Partitions(n):
            operators[(-1,nu)] = [make_deriv_comp_young(X[0][i],nu) for i in range(0,n)]
        F = Subspace(generators={(dim,Partition([1 for i in range(n)])):[Delta]},operators=operators,
                                    add_degrees=self.add_degree_isotyp, verbose=verbose)
        basis = F.basis()
        if self._use_antisymmetry:
            for d,B in basis.iteritems():
                pos = antisymmetries_of_tableau(d[1])
                res = [reduce_antisymmetric_normal(p,n,1,pos) for p in B]
                basis[d] = res
        return basis
        
        
