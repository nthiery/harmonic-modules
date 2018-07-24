#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.parallel.decorate import parallel
from sage.combinat.ranker import rank_from_list

from utilities import index_filling
from diagonal_polynomial_ring import *
from polynomial_derivative import *
from polarization_space import add_degree_symmetric, add_degree
from polarization_space import *


####################################################
# Harmonic Polynomials
####################################################

class DiagonalHarmonicPolynomials():
    """

        The space diagonal hamonic polynomials in n x r variables.

        EXAMPLES::

            sage: P = DiagonalHarmonicPolynomialRing(QQ, 4, 3)
            sage:
    """
    def __init__(self, R, n, r, antisymmetries=None):
        self._R = R
        self._n = n
        self._r = r
        self._antisymmetries = antisymmetries
        if antisymmetries: 
            self._polRing = DiagonalAntisymmetricPolynomialRing(R, n, r, antisymmetries)
        else:
            self._polRing = DiagonalPolynomialRing(R, n, r)
            
    def _repr_(self):
        """
            sage:

        """
        return "Diagonal harmonic polynomials with %s rows of %s variables over %s"%(self._r, self._n, self._polRing.base_ring())

    def harmonic_space_by_shape(self, mu, verbose=False, use_antisymmetry=False, use_symmetry=False, use_lie=False, use_commutativity=False):
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
        r = self._r
        S = SymmetricFunctions(ZZ)
        s = S.s()
        m = S.m()
        generators = [self.higher_specht(t, harmonic=True, use_antisymmetry=use_antisymmetry)
                      for t in StandardTableaux(mu)]

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
        # PROBLEM HERE with add_degree
        add_degree = add_degree_symmetric if use_symmetry else add_degree
        F = Subspace(generators, operators=operators,
                     add_degrees=add_degree, degree=self.multidegree,
                     hilbert_parent = hilbert_parent,
                     extend_word=extend_word, verbose=verbose)
        F._antisymmetries = antisymmetries
        return F
        
        def e(self, i):
            return functools.partial(self.polarization, i1=i, i2=i+1, d=1)

    def f(self, i):
        return functools.partial(self.polarization, i1=i+1, i2=i, d=1)

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

    def harmonic_character(self, mu, verbose=False, use_symmetry=False, use_antisymmetry=False, use_lie=False, use_commutativity=False):
        """
        Return the `GL_r` character of the space of diagonally harmonic polynomials
        contributed by a given `S_n` irreducible representation.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,5,2)
            sage: P.harmonic_character(Partition([3,2]))
            s[2] + s[2, 1] + s[2, 2] + s[3] + s[3, 1] + s[4] + s[4, 1] + s[5] + s[6]
        """
        mu = Partition(mu)
        F = self.harmonic_space_by_shape(mu, verbose=verbose,
                                         use_symmetry=use_symmetry,
                                         use_antisymmetry=use_antisymmetry,
                                         use_lie=use_lie,
                                         use_commutativity=use_commutativity)
        F.finalize()

        if use_lie != "euler+intersection":
            return F.hilbert_polynomial()
        # Otherwise:
        # The hilbert polynomial is expressed directly in terms of the
        # dimensions of the highest weight spaces; however the subspaces that
        # have been computed at this stage may include non highest weight
        # vectors.
        # We compute the intersection with the highest weight space,
        # i.e. the joint kernel of the f operators of the lie algebra
        # which are the polarization operators of degree 0 with i_2 < i_1
        operators = [functools.partial(self.polarization, i1=i1, i2=i2, d=1,
                                       antisymmetries=F._antisymmetries)
                     for i1 in range(1, self._r)
                     for i2 in range(i1)]
        return F._hilbert_parent({mu: len(annihilator_basis(basis._basis, operators, action=lambda b, op: op(b), ambient=self))
                                  for mu, basis in F._bases.iteritems() if basis._basis})

    def harmonic_bicharacter(self, verbose=False, use_symmetry=False, use_antisymmetry=False, use_lie=False):
        """
        Return the `GL_r-S_n` character of the space of diagonally harmonic polynomials

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,3,2)
            sage: P.harmonic_bicharacter()
            s[] # s[3] + s[1] # s[2, 1] + s[1, 1] # s[1, 1, 1] + s[2] # s[2, 1] + s[3] # s[1, 1, 1]

        """
        s = SymmetricFunctions(ZZ).s()
        def char(mu):
            if verbose:
                print "%s:"%s(mu)
            r = tensor([self.harmonic_space_by_shape(mu, verbose=verbose,
                                                     use_symmetry=use_symmetry,
                                                     use_antisymmetry=use_antisymmetry,
                                                     use_lie=use_lie,
                                                    ).hilbert_polynomial(),
                        s[mu]])
            return r
        # TODO Understand why this does not work in parallel
        #char = parallel()(char)
        #return sum( res[1] for res in char(Partitions(self._n).list()) )
        return sum(char(mu) for mu in Partitions(self._n))
    
    
####################################################
# Higher Specht
####################################################



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




####################################################
# Harmonic Polynomials With Inert Variables
####################################################

#TODO : find a (short) name for those polynomials
class DiagonalHarmonicPolynomialsInert():
    """

        The space of diagonal hamonic polynomials in n x r variables and k rows of inert variables

        EXAMPLES::

            sage: 
    """

    def __init__(self, R, n, r, inert=0, antisymmetries=None):
        self._antisymmetric = antisymmetric
        self._R = R
        self._n = n
        self._r = r
        self._k = inert
        self._inert = inert
        self._antisymmetries = antisymmetries
        if antisymmetries: 
            self._polRing = DiagonalAntisymmetricPolynomialRing(R, n, r, inert, antisymmetries)
        else:
            self._polRing = DiagonalPolynomialRing(R, n, r, inert)
            
    def _repr_(self):
        """

        """
        return "Diagonal harmonic polynomials with %s rows of %s variables and %s rows of inert variables over %s"%(self._r, self._n, self._k, self._polRing.base_ring())

    def vandermonde(self,mu):
        """
            Let `mu` be a diagram (of a partition or no) and $X=(x_i)$ and
            $\Theta = (\theta_i)$ two sets of n variables.
            Then $\Delta$ is the determinant of the matrix $(x_i^a\theta_i^b)$
            for (a,b) the cells of `mu`.

            INPUT: A partition `mu`

            OUTPUT: The determinant Delta

            EXAMPLES::
                sage: vandermonde([3])
                -x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2
                sage: vandermonde([2,1])
                -x01*x20 + x02*x20 + x00*x21 - x02*x21 - x00*x22 + x01*x22
                sage: vandermonde([1,1,1])
                -x20^2*x21 + x20*x21^2 + x20^2*x22 - x21^2*x22 - x20*x22^2 + x21*x22^2

        """
        n = self._n
        X = self._polRing.variables()
        Theta = self._polRing.inert_variables()
        if not isinstance(mu,Diagram):
            mu = Diagram(mu)
        Delta = matrix([[x**i[1]*theta**i[0] for i in mu.cells()] for x,theta in zip(X[0],Theta[0])]).determinant()
        return Delta

    def dimension_vandermonde(self,mu):
        return sum([i[1] for i in mu.cells()])
    
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
    def isotypic_basis(self,mu,verbose=True):
        """
            Let $W$ be the smallest submodule generated by a Vandermonde $\Delta$ depending on
            a partition`mu` and closed under partial derivatives.
            Then $W$ can be decomposed into isotypic components for the action of $S_n$. This function
            compute the basis of W using the Young idempotents to project on isotypic components.

            EXAMPLES::
                sage: DP = DiagonalPolynomialRing(QQ,3,2,inert=1)
                sage: DP.isotypic_basis(Partition([2,1]),use_antisymmetries=True,verbose=False)
                {(0, [2, 1]): [-3*x20], (1, [1, 1, 1]): [x00*x21]}
                sage: DP.isotypic_basis(Partition([3]),use_antisymmetries=True,verbose=False)

                {(0, [3]): [108],
                 (1, [2, 1]): [-18*x00],
                 (2, [2, 1]): [-3*x00^2 + 6*x00*x01],
                 (3, [1, 1, 1]): [-x00^2*x01]}

        """
        n = self._n
        r = self._r
        X = self._polRing.variables()
        charac = 0
        s = SymmetricFunctions(self._R).s()
        Delta = self.vandermonde(mu)
        dim = self.dimension_vandermonde(mu)
        operators = {}
        for nu in Partitions(n):
            operators[(-1,nu)] = [make_deriv_comp_young(X[0][i],nu) for i in range(0,n)]
        F = Subspace(generators={(dim,Partition([1 for i in range(n)])):[Delta]},operators=operators,
                                    add_degrees=self.add_degree_isotyp, verbose=verbose)
        basis = F.basis()
        if self._antisymmetries:
            for d,B in basis.iteritems():
                pos = antisymmetries_of_tableau(d[1])
                res = [reduce_antisymmetric_normal(p,n,r,pos) for p in B]
                basis[d] = res
        return basis


##################################################
# Harmonic characters
##################################################

def harmonic_character_plain(mu, verbose=False, parallel=False):
    import tqdm
    mu = Partition(mu)
    n = mu.size()
    if len(mu) == n:
        r = n-1
    else:
        r = n-2
    r = max(r, 1)
    R = DiagonalPolynomialRing(QQ, n, r)
    if verbose:
        progressbar = tqdm.tqdm(unit=" extensions", leave=True, desc="harmonic character for "+str(mu).ljust(mu.size()*3), position=mu.rank() if parallel else 1)
    else:
        progressbar = False
    result = R.harmonic_character(mu, verbose=progressbar,
                                  use_symmetry=True,
                                  use_lie=True,
                                  use_antisymmetry=True)
    return {tuple(degrees): dim
            for degrees, dim in result}

def harmonic_character_plain_key(mu, **args):
    return tuple(Partition(mu))
def harmonic_character_plain_hash(mu):
    return str(list(mu)).replace(" ","")[1:-1]
harmonic_character_plain = func_persist(harmonic_character_plain,
                                        hash=harmonic_character_plain_hash,
                                        key= harmonic_character_plain_key)

"""
Migrating persistent database from previous format::

    sage: SymmetricFunctions(ZZ).inject_shorthands()             # not tested
    sage: myhash=lambda mu: str(list(mu)).replace(" ","")[1:-1]
    sage: cd func_persist                                        # not tested
    sage: for filename in glob.glob("harmonic_character*.sobj"): # not tested
    ....:     obj = load(filename)
    ....:     key = obj[0][0][0]
    ....:     value = obj[1]
    ....:     chi = s(m.sum_of_terms([Partition(nu), c] for nu, c in value.iteritems())).restrict_partition_lengths(max(4, len(key)-1), exact=False)
    ....:     print key, chi
    ....:     value = {tuple(nu):c for nu,c in chi }
    ....:     save((key,value), "plain/harmonic_character_plain_%s"%(myhash(key)))

Inserting François's value for the character for `1^6` in the database::

    sage: S = SymmetricFunctions(ZZ)
    sage: s = S.s()
    sage: res = s[1, 1, 1, 1, 1] + s[3, 1, 1, 1] + s[4, 1, 1, 1] + s[4, 2, 1] + s[4, 3, 1] + s[4, 4] + s[4, 4, 1] + s[5, 1, 1, 1] + s[5, 2, 1] + s[5, 3, 1] + s[6, 1, 1] + s[6,1, 1, 1] + s[6, 2, 1] + s[6, 3] + s[6, 3, 1] + s[6, 4] + s[7, 1, 1] + s[7, 2] +s[7, 2, 1] + s[7, 3] + s[7, 4] + 2*s[8, 1, 1] + s[8, 2] + s[8, 2, 1] + s[8, 3] + s[9, 1, 1] + s[9, 2] + s[9, 3] + s[10, 1] + s[10, 1, 1] + s[10, 2] + s[11, 1] + s[11, 2] + s[12, 1] + s[13, 1] + s[15]
    sage: key=tuple([1,1,1,1,1,1])
    sage: value = {tuple(mu):c for mu,c in res}
    sage: myhash=lambda mu: str(list(mu)).replace(" ","")[1:-1]
    sage: save((key,value), "func_persist/harmonic_character_plain_%s"%(myhash(key))) # not tested
"""

def harmonic_character(mu):
    """
    Return the `GL_n` character of an `S_n` isotypic component in the
    diagonal harmonic polynomials

    Let `H` be the space of diagonal harmonic harmonic polynomials on
    `k\times n` variables, with `k` large enough.  Write its `GL_k
    \times S_n` bicharacter as `\sum f_\mu \otimes s_\mu`.  This
    computes `f_\mu`.

    EXAMPLES::

        sage: harmonic_character([6])
        s[]
        sage: harmonic_character([5, 1])
        s[1] + s[2] + s[3] + s[4] + s[5]
        sage: harmonic_character([4, 2])
        s[2] + s[2, 1] + s[2, 2] + s[3] + s[3, 1] + s[3, 2] + 2*s[4] + 2*s[4, 1] + s[4, 2] + s[5] + s[5, 1] + 2*s[6] + s[6, 1] + s[7] + s[8]
        sage: harmonic_character([4, 1, 1])
        s[1, 1] + s[2, 1] + s[3] + 2*s[3, 1] + s[3, 2] + s[3, 3] + s[4] + 2*s[4, 1] + s[4, 2] + 2*s[5] + 2*s[5, 1] + s[5, 2] + 2*s[6] + s[6, 1] + 2*s[7] + s[7, 1] + s[8] + s[9]
        sage: harmonic_character([3, 3])
        s[2, 2] + s[2, 2, 1] + s[3] + s[3, 1] + s[3, 2] + s[4, 1] + s[4, 1, 1] + s[4, 2] + s[5] + s[5, 1] + s[5, 2] + s[6] + s[6, 1] + s[7] + s[7, 1] + s[9]
        sage: harmonic_character([2, 2, 2])
        s[2, 2] + s[2, 2, 1] + s[3, 1, 1] + s[3, 1, 1, 1] + s[3, 2, 1] + s[3, 3, 1] + s[4, 1] + s[4, 1, 1] + 2*s[4, 2] + s[4, 2, 1] + s[4, 3] + s[4, 4] + s[5, 1] + 2*s[5, 1, 1] + 2*s[5, 2] + s[5, 2, 1] + s[5, 3] + s[6] + 2*s[6, 1] + s[6, 1, 1] + 2*s[6, 2] + s[6, 3] + 2*s[7, 1] + s[7, 1, 1] + s[7, 2] + s[8] + 2*s[8, 1] + s[8, 2] + s[9] + s[9, 1] + s[10] + s[10, 1] + s[12]
        sage: harmonic_character([3, 1, 1, 1])
        s[1, 1, 1] + s[2, 1, 1] + s[3, 1] + 2*s[3, 1, 1] + s[3, 2] + s[3, 2, 1] + 2*s[3, 3] + s[3, 3, 1] + 2*s[4, 1] + 2*s[4, 1, 1] + 2*s[4, 2] + s[4, 2, 1] + 2*s[4, 3] + 3*s[5, 1] + 2*s[5, 1, 1] + 3*s[5, 2] + s[5, 2, 1] + 2*s[5, 3] + s[6] + 4*s[6, 1] + s[6, 1, 1] + 3*s[6, 2] + s[6, 3] + s[7] + 4*s[7, 1] + s[7, 1, 1] + 2*s[7, 2] + 2*s[8] + 3*s[8, 1] + s[8, 2] + 2*s[9] + 2*s[9, 1] + 2*s[10] + s[10, 1] + s[11] + s[12]
        sage: harmonic_character([3, 2, 1])
        s[2, 1] + s[2, 1, 1] + s[2, 2] + s[2, 2, 1] + 2*s[3, 1] + 2*s[3, 1, 1] + 3*s[3, 2] + 2*s[3, 2, 1] + s[3, 3] + s[4] + 3*s[4, 1] + 2*s[4, 1, 1] + 4*s[4, 2] + s[4, 2, 1] + 2*s[4, 3] + 2*s[5] + 5*s[5, 1] + 2*s[5, 1, 1] + 4*s[5, 2] + s[5, 3] + 2*s[6] + 5*s[6, 1] + s[6, 1, 1] + 3*s[6, 2] + 3*s[7] + 4*s[7, 1] + s[7, 2] + 3*s[8] + 3*s[8, 1] + 2*s[9] + s[9, 1] + 2*s[10] + s[11]
        sage: harmonic_character([2, 1, 1, 1, 1])
        s[1, 1, 1, 1] + s[2, 1, 1, 1] + s[3, 1, 1] + s[3, 1, 1, 1] + s[3, 2, 1] + s[3, 3, 1] + 2*s[4, 1, 1] + s[4, 1, 1, 1] + s[4, 2] + 2*s[4, 2, 1] + 2*s[4, 3] + 2*s[4, 3, 1] + s[4, 4] + 3*s[5, 1, 1] + s[5, 1, 1, 1] + s[5, 2] + 2*s[5, 2, 1] + 2*s[5, 3] + s[5, 3, 1] + s[5, 4] + s[6, 1] + 3*s[6, 1, 1] + 3*s[6, 2] + 2*s[6, 2, 1] + 3*s[6, 3] + s[6, 4] + 2*s[7, 1] + 3*s[7, 1, 1] + 3*s[7, 2] + s[7, 2, 1] + 2*s[7, 3] + 3*s[8, 1] + 2*s[8, 1, 1] + 3*s[8, 2] + s[8, 3] + 3*s[9, 1] + s[9, 1, 1] + 2*s[9, 2] + s[10] + 3*s[10, 1] + s[10, 2] + s[11] + 2*s[11, 1] + s[12] + s[12, 1] + s[13] + s[14]
        sage: harmonic_character([2, 2, 1, 1])
        s[2, 1, 1] + s[2, 1, 1, 1] + s[2, 2, 1] + s[3, 1, 1] + s[3, 1, 1, 1] + s[3, 2] + 2*s[3, 2, 1] + s[3, 3] + s[3, 3, 1] + s[4, 1] + 3*s[4, 1, 1] + s[4, 1, 1, 1] + 2*s[4, 2] + 3*s[4, 2, 1] + 2*s[4, 3] + s[4, 3, 1] + s[4, 4] + 2*s[5, 1] + 3*s[5, 1, 1] + 4*s[5, 2] + 2*s[5, 2, 1] + 3*s[5, 3] + s[5, 4] + 3*s[6, 1] + 4*s[6, 1, 1] + 4*s[6, 2] + s[6, 2, 1] + 2*s[6, 3] + s[7] + 4*s[7, 1] + 2*s[7, 1, 1] + 4*s[7, 2] + s[7, 3] + s[8] + 4*s[8, 1] + s[8, 1, 1] + 2*s[8, 2] + 2*s[9] + 4*s[9, 1] + s[9, 2] + s[10] + 2*s[10, 1] + 2*s[11] + s[11, 1] + s[12] + s[13]
        sage: harmonic_character([1, 1, 1, 1, 1, 1])
        s[1, 1, 1, 1, 1] + s[3, 1, 1, 1] + s[4, 1, 1, 1] + s[4, 2, 1] + s[4, 3, 1] + s[4, 4] + s[4, 4, 1] + s[5, 1, 1, 1] + s[5, 2, 1] + s[5, 3, 1] + s[6, 1, 1] + s[6, 1, 1, 1] + s[6, 2, 1] + s[6, 3] + s[6, 3, 1] + s[6, 4] + s[7, 1, 1] + s[7, 2] + s[7, 2, 1] + s[7, 3] + s[7, 4] + 2*s[8, 1, 1] + s[8, 2] + s[8, 2, 1] + s[8, 3] + s[9, 1, 1] + s[9, 2] + s[9, 3] + s[10, 1] + s[10, 1, 1] + s[10, 2] + s[11, 1] + s[11, 2] + s[12, 1] + s[13, 1] + s[15]
    """
    mu = tuple(mu)
    result = harmonic_character_plain(mu)
    S = SymmetricFunctions(ZZ)
    s = S.s()
    return s.sum_of_terms([Partition(d), c] for d,c in result.iteritems())

@parallel()
def harmonic_character_paral(mu):
    r"""
    Utility to parallelize the computation of the `GL_r` character of
    the `S_n` isotypic components in the diagonal harmonic
    polynomials.
    """
    t1 = datetime.datetime.now()
    result = harmonic_character_plain(mu, verbose=True, parallel=True)
    t2 = datetime.datetime.now()
    return result, t2-t1

def harmonic_characters(n):
    r"""
    Compute in parallel the `GL_r` character of all `S_n` isotypic
    components in the diagonal harmonic polynomials.
    """
    S = SymmetricFunctions(ZZ)
    s = S.s()
    for (((nu,),_), (result, t)) in harmonic_character_paral((tuple(mu),) for mu in Partitions(n)):
        import tqdm
        tqdm.tqdm.write("\r%s\t("%Partition(nu)+str(t)[:-7]+"): %s"%
                                                     s.sum_of_terms([Partition(d), c]
                                                                    for d,c in result.iteritems()))

def harmonic_bicharacter(n):
    s = SymmetricFunctions(ZZ).s()
    ss = tensor([s,s])
    return ss.sum(tensor([harmonic_character(mu), s.term(mu)])
                  for mu in Partitions(n))

def harmonic_bicharacter_truncated_series():
    """
    Return the diagonal harmonic bicharacter series, truncated to
    whatever has already been computed and stored in the database.

    OUTPUT: a sum `\sum c_{\lambda,\mu} s_\lambda \tensor s_\mu`

    EXAMPLES::

        sage: Harm = harmonic_bicharacter_truncated_series()

        sage: Sym = SymmetricFunctions(ZZ)
        sage: s = Sym.s(); e = Sym.e(); h = Sym.h()

    Extracting the `S_n` character for a given `GL_r` representation::

        sage: def chi1(mu, p):
        ....:     return s.sum_of_terms([nu,c] for ((mu1,nu),c) in p if mu1 == mu)
        sage: def chi2(nu, p):
        ....:     return e.sum_of_terms([mu,c] for ((mu,nu1),c) in p if nu1 == nu)
        sage: chi1([1,1], Harm)
        s[1, 1, 1] + s[2, 1, 1] + s[3, 1, 1] + s[4, 1, 1]

    Some steps toward recovering it as a product H * finite sum.
    Let's define `H` and its inverse::

        sage: H = sum(h[i] for i in range(0, 10)); H
        h[] + h[1] + h[2] + h[3] + h[4] + h[5] + h[6] + h[7] + h[8] + h[9]
        sage: Hinv = s(1-e[1]+e[2]-e[3]+e[4]-e[5]+e[6])

        sage: truncate(H*Hinv,6)
        h[]

        sage: truncate((1-chi1([1], Harm)    ) * Hinv, 7)
        s[] - s[1]

        sage: truncate((1+chi1([1,1], Harm)  ) * Hinv, 7)
        s[] - s[1] + s[1, 1]

        sage: truncate((1-chi1([1,1,1], Harm)) * Hinv, 7)
        s[] - s[1] + s[1, 1] - s[1, 1, 1]



        sage: bitruncate(Harm * tensor([s.one(), (1-s[1]+s[2]-s[3]+s[4]-s[5])]), 6)
        s[] # s[] - s[] # s[1, 1] + s[] # s[2] + s[] # s[2, 2] - s[] # s[3, 1] + s[] # s[4] + s[1] # s[1, 1] - s[1] # s[1, 1, 1] - s[1] # s[2, 2] + s[1] # s[2, 2, 1] + s[1] # s[3, 1] - s[1] # s[3, 1, 1] + s[1, 1] # s[1, 1, 1] - s[1, 1] # s[1, 1, 1, 1] - s[1, 1] # s[2, 2, 1] + s[1, 1] # s[3, 1, 1] + s[1, 1, 1] # s[1, 1, 1, 1] - s[1, 1, 1] # s[1, 1, 1, 1, 1] + s[1, 1, 1, 1] # s[1, 1, 1, 1, 1] + s[2] # s[2, 1] - s[2] # s[2, 1, 1] + s[2] # s[4, 1] + s[2, 1] # s[2, 1, 1] - s[2, 1] # s[2, 1, 1, 1] + s[2, 1] # s[2, 2] - s[2, 1] # s[2, 2, 1] + s[2, 1, 1] # s[2, 1, 1, 1] + s[2, 1, 1] # s[2, 2, 1] + s[2, 2] # s[2, 2, 1] + s[2, 2] # s[3, 2] + s[3] # s[1, 1, 1] - s[3] # s[1, 1, 1, 1] - s[3] # s[2, 2, 1] + s[3] # s[3, 1] + s[3, 1] # s[1, 1, 1, 1] - s[3, 1] # s[1, 1, 1, 1, 1] + s[3, 1] # s[2, 1, 1] - s[3, 1] # s[2, 1, 1, 1] + s[3, 1] # s[3, 1, 1] + s[3, 1] # s[3, 2] + s[3, 1, 1] # s[1, 1, 1, 1, 1] + s[3, 1, 1] # s[2, 1, 1, 1] + s[3, 1, 1] # s[2, 2, 1] + s[3, 2] # s[2, 1, 1, 1] + s[3, 2] # s[2, 2, 1] + s[3, 2] # s[3, 1, 1] + s[4] # s[2, 1, 1] - s[4] # s[2, 1, 1, 1] + s[4] # s[2, 2] - s[4] # s[2, 2, 1] + s[4] # s[4, 1] + s[4, 1] # s[1, 1, 1, 1] - s[4, 1] # s[1, 1, 1, 1, 1] + s[4, 1] # s[2, 1, 1, 1] + 2*s[4, 1] # s[2, 2, 1] + s[4, 1] # s[3, 1, 1] + s[4, 1] # s[3, 2] + s[5] # s[2, 1, 1] - s[5] # s[2, 1, 1, 1] + s[5] # s[3, 1, 1] + s[5] # s[3, 2]

    Not quite::

        sage: bitruncate(Harm * tensor([s.one(), Hinv]), 6)
        s[] # s[] + s[1] # s[1, 1] - s[1] # s[1, 1, 1] + s[1] # s[1, 1, 1, 1] - s[1] # s[1, 1, 1, 1, 1] + s[1, 1] # s[1, 1, 1] - s[1, 1] # s[1, 1, 1, 1] + s[1, 1] # s[1, 1, 1, 1, 1] + s[1, 1, 1] # s[1, 1, 1, 1] - s[1, 1, 1] # s[1, 1, 1, 1, 1] + s[1, 1, 1, 1] # s[1, 1, 1, 1, 1] + s[2] # s[2, 1] - s[2] # s[2, 1, 1] + s[2] # s[2, 1, 1, 1] + s[2, 1] # s[2, 1, 1] - s[2, 1] # s[2, 1, 1, 1] + s[2, 1] # s[2, 2] - s[2, 1] # s[2, 2, 1] + s[2, 1, 1] # s[2, 1, 1, 1] + s[2, 1, 1] # s[2, 2, 1] + s[2, 2] # s[2, 2, 1] + s[2, 2] # s[3, 2] + s[3] # s[1, 1, 1] - s[3] # s[1, 1, 1, 1] + s[3] # s[1, 1, 1, 1, 1] + s[3] # s[3, 1] - s[3] # s[3, 1, 1] + s[3, 1] # s[1, 1, 1, 1] - s[3, 1] # s[1, 1, 1, 1, 1] + s[3, 1] # s[2, 1, 1] - s[3, 1] # s[2, 1, 1, 1] + s[3, 1] # s[3, 1, 1] + s[3, 1] # s[3, 2] + s[3, 1, 1] # s[1, 1, 1, 1, 1] + s[3, 1, 1] # s[2, 1, 1, 1] + s[3, 1, 1] # s[2, 2, 1] + s[3, 2] # s[2, 1, 1, 1] + s[3, 2] # s[2, 2, 1] + s[3, 2] # s[3, 1, 1] + s[4] # s[2, 1, 1] - s[4] # s[2, 1, 1, 1] + s[4] # s[2, 2] - s[4] # s[2, 2, 1] + s[4] # s[4, 1] + s[4, 1] # s[1, 1, 1, 1] - s[4, 1] # s[1, 1, 1, 1, 1] + s[4, 1] # s[2, 1, 1, 1] + 2*s[4, 1] # s[2, 2, 1] + s[4, 1] # s[3, 1, 1] + s[4, 1] # s[3, 2] + s[5] # s[2, 1, 1] - s[5] # s[2, 1, 1, 1] + s[5] # s[3, 1, 1] + s[5] # s[3, 2]


    Substituting `q_n=1` (which should be equivalent to computing the plethysm on `X+1`)
    gives an e-positive expression (TODO: see why this is currently broken)::

        sage: res = tensor([s,e])( sum(c*tensor( [s[mu](s[1] + 1), s[nu]] ) for ((mu, nu), c) in Harm) )   # not tested
        sage: set(res.coefficients())                                                                      # not tested
        {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}
    """
    s = SymmetricFunctions(ZZ).s()
    ss = tensor([s,s])
    return ss.sum_of_terms([(Partition(mu), Partition(nu)), c]
                           for nu,d in harmonic_character_plain.dict().iteritems()
                           for mu,c in d.iteritems())

def truncate(f,d):
    return f.map_support_skip_none(lambda mu: mu if mu.size() < d else None)

def bitruncate(f,d):
    return f.map_support_skip_none(lambda (mu,nu): (mu,nu) if mu.size() < d and nu.size() < d else None)


###########################################################
# Characters with inert variables
###########################################################

        
def character_with_inert(mu,parallel=True): 
    """
        Return the complete character of the smallest submodule generated by $\Delta_{\mu}$
        and closed under partial derivatives and polarization operators for the double action
        of $GL_r \times S_n$. 
        The result is given as a sum of tensor product of Schur functions.
        
        EXAMPLES::
        sage: character_with_inert(Partition([3]))
        s[] # s[3] + s[1] # s[2, 1] - s[1, 1] # s[2, 1] + s[2] # s[2, 1] - s[2, 1] # s[1, 1, 1] + s[3] # s[1, 1, 1]
        sage: character_with_inert(Partition([2,1]))
        s[] # s[2, 1] + s[1] # s[1, 1, 1]
        sage: character_with_inert(Partition([1,1,1,1]))
        s[] # s[1, 1, 1, 1]

    """
    n = mu.size()
    r = mu.size()
    DPRI = DiagonalPolynomialRingInert(QQ,n,r)
    return character_schur(DPRI,mu,parallel=parallel)
        
def character_key(mu, **args):
    return tuple(Composition(mu))
def character_hash(mu):
    return str(list(mu)).replace(" ","")[1:-1]
character_with_inert = func_persist(character_with_inert,hash=character_hash,key=character_key)


def into_schur(P,charac):
    """
        Convert a character `charac` written as a sum of tensor products of polynomials in q
        variables and Schur functions into a character written as a sum of tensor products
        of Schur functions.

        INPUT: `charac` a sum of tensor products

        EXAMPLES::
            sage: for c in [DP.character_q_parallel(p) for p in Partitions(3)]:
            ....:     print DP.into_schur(c)
            s[] # s[3] + s[1] # s[2, 1] + s[1, 1] # s[1, 1, 1] + s[2] # s[1, 1, 1] + s[2] # s[2, 1] + s[3] # s[1, 1, 1]
            s[] # s[2, 1] + s[1] # s[1, 1, 1]
            s[] # s[1, 1, 1]

    """
    
    nb_rows = P._n - P._k
    s = SymmetricFunctions(P._Q).s()
    ss = SymmetricFunctions(QQ).s()
    sym_char = 0
    for supp in charac.support():
        if charac.coefficient(supp)==1:
            sym_char += tensor([s[0],s[supp]])
        else:
            sym_char += tensor([s(ss.from_polynomial(P._Q(charac.coefficient(supp))))
                                .restrict_partition_lengths(nb_rows,exact=False),s[supp]])
    return sym_char

def character_schur(P,mu,parallel=True,verbose=True):
    """
        Return the complete character of the smallest submodule generated by $\Delta_{\mu}$
        and closed under partial derivatives and polarization operators for the double action
        of $GL_r \times S_n$.
        The result is given as a sum of tensor product of Schur functions.

        EXAMPLES::
        sage: DP = DiagonalPolynomialRingInert(QQ,3,3)
        sage: DP.character_schur(Partition([3]))
        s[] # s[3] + s[1] # s[2, 1] + s[1, 1] # s[1, 1, 1] + s[2] # s[1, 1, 1] + s[2] # s[2, 1] + s[3] # s[1, 1, 1]
        sage: DP = DiagonalPolynomialRingInert(QQ,4,4)
        sage: DP.character_schur(Partition([2,2]))
        s[] # s[2, 2] + s[1] # s[2, 1, 1] + s[2] # s[1, 1, 1, 1]

    """

    return into_schur(P,self.character_q(mu,parallel=parallel))
