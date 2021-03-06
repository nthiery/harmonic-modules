#!/usr/bin/env python
# -*- coding: utf-8 -*-

import functools

from sage.misc.cachefunc import cached_method, cached_function
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.sage_object import load

from sage.parallel.decorate import parallel
from sage.misc.misc_c import prod

from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.categories.isomorphic_objects import IsomorphicObjectsCategory
from sage.categories.algebras import Algebras
from sage.categories.cartesian_product import cartesian_product
from sage.functions.other import binomial
from sage.combinat.words.word import Word
from sage.matrix.constructor import matrix

from isomorphic_object import *
from polynomial_derivative import *

from utilities import *
from antisymmetric_utilities import *

##############################################################################
# Polynomial ring with diagonal action
##############################################################################

class DiagonalPolynomialRing(UniqueRepresentation, Parent):
    """
    The ring of diagonal polynomials in $n \times r$ variables and $n \times k$ inert variables.
    In order to distinguish the inert variables among the others, they are named `theta_{i,j}`

    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ, 4, 3)
        sage: P
        Diagonal polynomial ring with 3 rows of 4 variables over Rational Field

        sage: P = DiagonalPolynomialRing(QQ, 4, 3, inert=1)
        sage: P
        Diagonal polynomial ring with 3 rows of 4 variables and 1 row(s) of inert variables over Rational Field

    """
    def __init__(self, R, n, r, inert=0):
        names = ["x%s%s"%(i,j) for i in range(r) for j in range(n)]+["theta%s%s"%(i,j) for i in range(inert) for j in range(n)]
        P = PolynomialRing(R, n*(r+inert), names)
        self._n = n
        self._r = r
        self._inert = inert
        vars = P.gens()
        self._P = P
        self._R = R
        self._Q = PolynomialRing(QQ,'q',r)
        self._grading_set = cartesian_product([ZZ for i in range(r)])
        self._hilbert_parent = PolynomialRing(ZZ, r, 'q')
        self._vars = matrix([[vars[i*n+j] for j in range(n)] for i in range(r+inert)])
        self._X = matrix([[vars[i*n+j] for j in range(n)] for i in range(r)])
        self._Theta = matrix([[vars[i*n+j] for j in range(n)] for i in range(r,r+inert)])
        Parent.__init__(self, facade=(P,), category=Algebras(QQ).Commutative())

    def _repr_(self):
        """
        sage: DiagonalPolynomialRing(QQ, 5, 3)
        Diagonal polynomial ring with 3 rows of 5 variables over Rational Field
        sage: DiagonalPolynomialRing(QQ, 4, 3, inert=1)
        Diagonal polynomial ring with 3 rows of 4 variables and 1 row(s) of inert variables over Rational Field

        """
        if self._inert == 0 :
            return "Diagonal polynomial ring with %s rows of %s variables over %s"%(self._r, self._n, self.base_ring())
        else :
            return "Diagonal polynomial ring with %s rows of %s variables and %s row(s) of inert variables over %s"%(self._r, self._n, self._inert, self.base_ring())

    def base_ring(self):
        """
        sage: D = DiagonalPolynomialRing(QQ, 4, 3)
        sage: D.base_ring()
        Rational Field

        """
        return self._P.base_ring()
        
        
    def gens(self):
        """
        sage: D = DiagonalPolynomialRing(QQ, 4, 3, inert=1)
        sage: D.gens()
        (q0, q1, q2)
        """
        return self._Q.gens()


    def algebra_generators(self):
        """
        Return all the variables including the inert variables.
        
        EXAMPLES ::
        
            sage: D = DiagonalPolynomialRing(QQ, 4, 3, inert=1)
            sage: D
            Diagonal polynomial ring with 3 rows of 4 variables and 1 row(s) of inert variables over Rational Field
            sage: D.algebra_generators()
            [    x00     x01     x02     x03]
            [    x10     x11     x12     x13]
            [    x20     x21     x22     x23]
            [theta00 theta01 theta02 theta03]
            
            sage: D = DiagonalPolynomialRing(QQ, 4, 3)
            sage: D
            Diagonal polynomial ring with 3 rows of 4 variables over Rational Field
            sage: D.algebra_generators()
            [x00 x01 x02 x03]
            [x10 x11 x12 x13]
            [x20 x21 x22 x23]

        """
        return self._vars

    def variables(self):
        """
        Return only the classic variables.
        
        EXAMPLES::
            sage: DP = DiagonalPolynomialRing(QQ, 3, 3, inert=1)
            sage: DP.variables()
            [x00 x01 x02]
            [x10 x11 x12]
            [x20 x21 x22]
                
        """
        return self._X

    def inert_variables(self):
        """
        Return only the inert variables. 
        git trac config --user USERNAME --pass 'PASSWORD'
        EXAMPLES::
            sage: DP = DiagonalPolynomialRing(QQ, 3, 3, inert=1)
            sage: DP.inert_variables()
            [theta00 theta01 theta02]
            
            sage: DP = DiagonalPolynomialRing(QQ, 3, 3)
            sage: DP.inert_variables()
            'No inert variables'

        """
        if self._inert != 0:
            return self._Theta
        else:
            return "No inert variables"

    def inject_variables(self):
        self._P.inject_variables()

    def multidegree(self, p):
        """
        Return the multidegree of a multihomogeneous polynomial.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 3, 2)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[0,1]^2 * X[1,0]^2*X[1,1]^3
            sage: P.multidegree(p)
            (3, 5)
            sage: P.multidegree(P.zero())
            -1
            sage: P = DiagonalPolynomialRing(QQ, 3, 2, inert=1)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[0,1] * X[1,1]^3 * X[2,0]*X[2,1]^2 
            sage: P.multidegree(p)
            (2, 3)

        """
        if not p:
            return -1
        n = self._n
        r = self._r
        v = p.exponents()[0]
        return self._grading_set([sum(v[n*i+j] for j in range(n))
                                  for i in range(r)])
    
    def multipower(self,d):
        """
        Return the product of the terms $q_i^{d_i}$.
        
        INPUT:
            - `d` -- a multidegree
            
        EXAMPLES::
            sage: P = DiagonalPolynomialRing(QQ,4,3,inert=1)
            sage: d = [1, 0, 2]
            sage: P.multipower(d)
            q0*q2^2

            sage: P = DiagonalPolynomialRing(QQ,4,4)
            sage: d = [4,3,2,1]
            sage: P.multipower(d)
            q0^4*q1^3*q2^2*q3

        """
        q = self._Q.gens()
        return prod(q[i]**d[i] for i in range(0,len(q)))

    def monomial(self, *args):
        """
        # TODO NICOLAS add documentation
        """
        return self._P.monomial(*args)
    
    def random_monomial(self, D):
        """
        Return a random monomial of multidegree `D`

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,3,3)
            sage: D = (3,1,4)
            sage: P.random_monomial(D)          # random
            x00*x01*x02*x10*x20*x21^2*x22

            sage: for i in range(50):
            ....:     assert P.multidegree(P.random_monomial(D)) == D
        """
        X = self.algebra_generators()
        X_by_rows = [Set(list(row)) for row in X]
        return prod( X_by_rows[i].random_element()
                     for i in range(len(D))
                     for j in range(D[i]) )

    def random_element(self, D, l=10):
        """
        Return a "random" multi homogeneous polynomial of multidegree `D`.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,3,3)
            sage: P.random_element((2,0,1))         # random
            x01^2*x20 - x02^2*x20 - x00*x01*x21 - x02^2*x21 + 7/4*x00^2*x22 + x01^2*x22 + 183/184*x01*x02*x22
        """
        K = self.base_ring()
        return sum(K.random_element() * self.random_monomial(D)
                   for i in range(l))
                
    def row_permutation(self, sigma):
        """
        Return the permutation of the variables induced by a permutation of the rows

        INPUT:
        - ``sigma`` -- a permutation of the rows, as a permutation of `\{1,\ldots,r\}`

        OUTPUT: a permutation of the variables, as a permutation of `\{1,\ldots,nr\}`

        EXAMPLES::

            sage: s = PermutationGroupElement([(1,2,4),(3,5)])
            sage: P = DiagonalPolynomialRing(QQ,3,5)
            sage: P.row_permutation(s)
            (1,4,10)(2,5,11)(3,6,12)(7,13)(8,14)(9,15)
        """
        n = self._n
        return PermutationGroupElement([tuple((i-1)*n + 1 + j for i in c)
                                        for c in sigma.cycle_tuples()
                                        for j in range(n) ])

    def polarization(self, p, i1, i2, d, row_symmetry=None):
        """
        Return the polarization `P_{d,i_1,i_2}. p` of `p`.

        Recall that the polarization operator is defined by
        .. MATH:: P_{d,i_1,i_2} := \sum_j x_{i_2,j} \partial_{i_1,j}^d

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 3, 4)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[1,0]^3*X[1,1]^1 + X[2,1]; p
            x00*x10^3*x11 + x21

            sage: P.polarization(p, 1, 2, 2)
            6*x00*x10*x11*x20
            
            sage: P.polarization(p, 1, 2, 1)
            3*x00*x10^2*x11*x20 + x00*x10^3*x21
            sage: P.polarization(p, 1, 2, 1, row_symmetry="permutation")
            3*x00^2*x01*x10*x20 + x00^3*x10*x21

            sage: P.polarization(p, 1, 0, 2)
            6*x00^2*x10*x11

            sage: P.polarization(p, 2, 0, 1)
            x01
        """
        n = self._n
        X = self.variables()
        if i1>=self._r or i2 >=self._r:
            print "Row number out of range."
            return None
        else:
            result = self.sum(X[i2,j]*p.derivative(X[i1,j],d)
                              for j in range(n))
            if row_symmetry=="permutation" and result:
                d = self.multidegree(result)
                d = tuple(d) + tuple(0 for i in range(self._inert))
                if list(d) != sorted(d, reverse=True):
                    s = reverse_sorting_permutation(d)
                    ss = self.row_permutation(s)
                    result = act_on_polynomial(result, ss)
            return result
            
    def higher_polarization(self, p, i1, i2, d1, d2, row_symmetry=None):
        """
        Return the polarization `P_{d1,d2,i_1,i_2}. p` of `p`.

        Recall that the polarization operator is defined by
        .. MATH:: P_{d1,d2,i_1,i_2} := \sum_j x_{i_2,j}^d1 \partial_{i_1,j}^d1

        EXAMPLES::
            sage: P = DiagonalPolynomialRing(QQ, 3, 4)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[1,1]^2 - X[0,1]^2*X[1,0]
            sage: p
            -x01^2*x10 + x00*x11^2
            sage: P.higher_polarization(p, 0, 1, 1, 1)
            -2*x01*x10*x11 + x10*x11^2
            sage: P.higher_polarization(p, 0, 1, 1, 2)
            -2*x01*x10*x11^2 + x10^2*x11^2
            sage: P.higher_polarization(p, 0, 1, 2, 1)
            -2*x10*x11

        """
        n = self._n
        X = self.variables()
        if i1>=self._r or i2 >=self._r:
            print "Row number out of range."
            return None 
        elif d2<1 :
            print "Degree for second variable should be at least 1."
        else:
            result = self.sum((X[i2,j]**d2)*p.derivative(X[i1,j],d1)
                              for j in range(n))
            if row_symmetry=="permutation" and result:
                d = self.multidegree(result)
                d = tuple(d) + tuple(0 for i in range(self._inert))
                if list(d) != sorted(d, reverse=True):
                    s = reverse_sorting_permutation(d)
                    ss = self.row_permutation(s)
                    result = act_on_polynomial(result, ss)
            return result
            
    def symmetric_derivative(self, p, d, row_symmetry=None):
        """
        Return the symmetric derivative of p w.r.t the degrees d.
        
        INPUT :
            - p -- a polynomial in the variables of self
            - d -- a list of degree corresponding to the derivation degree 
                for each set of variables
                
        EXAMPLES::
            sage: P = DiagonalPolynomialRing(QQ, 3, 1)
            sage: x = P.variables()
            sage: v = -x[0,0]^3*x[0,1] + x[0,0]*x[0,1]^3 + x[0,0]^3*x[0,2] - x[0,1]^3*x[0,2] - x[0,0]*x[0,2]^3 + x[0,1]*x[0,2]^3; v
            -x00^3*x01 + x00*x01^3 + x00^3*x02 - x01^3*x02 - x00*x02^3 + x01*x02^3
            sage: P.symmetric_derivative(v, [1])
            -3*x00^2*x01 + 3*x00*x01^2 + 3*x00^2*x02 - 3*x01^2*x02 - 3*x00*x02^2 + 3*x01*x02^2
            sage: P.symmetric_derivative(v, [2])
            0
            sage: P.symmetric_derivative(v, [3])
            0
            
            sage: P = DiagonalPolynomialRing(QQ, 3, 2)
            sage: v = P(v)
            sage: v_pol = P.polarization(v, 0, 1, 1); v_pol
            -3*x00^2*x01*x10 + x01^3*x10 + 3*x00^2*x02*x10 - x02^3*x10 - x00^3*x11 + 3*x00*x01^2*x11 - 3*x01^2*x02*x11 + x02^3*x11 + x00^3*x12 - x01^3*x12 - 3*x00*x02^2*x12 + 3*x01*x02^2*x12
            sage: P.symmetric_derivative(v_pol, [1,1])
            0
            sage: P.symmetric_derivative(v_pol, [0,1])
            -3*x00^2*x01 + 3*x00*x01^2 + 3*x00^2*x02 - 3*x01^2*x02 - 3*x00*x02^2 + 3*x01*x02^2
            
        """
        n = self._n
        r = self._r
        X = self.variables()
        result = 0
        if not isinstance(d, (tuple, list)):
            d = [d]
        for i in range(n): #columns
            interm_result = p
            for j in range(len(d)): #rows
                interm_result = interm_result.derivative(X[j,i],d[j])
            result += interm_result
            
        if row_symmetry=="permutation" and result:
            deg = self.multidegree(result) 
            deg = tuple(deg) + tuple(0 for i in range(self._inert))
            if list(deg) != sorted(deg, reverse=True):
                s = reverse_sorting_permutation(deg)
                ss = self.row_permutation(s)
                result = act_on_polynomial(result, ss)
        return result
        
    def steenrod_op(self, p, i, k, row_symmetry=None):
        """
        Apply the Steenrod operator of degree `k` for the `i`th set of variables
        to `p`. 
        The Steenrod operator for a set of variables $x_1, x_2, dots, x_n$ is 
        given by 
        .. MATh:: \sum_i x_i \partial_{x_i}^{k+1}
        
        EXEMPLES::
            sage: P = DiagonalPolynomialRing(QQ, 3, 4)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[0,1] - X[0,1]*X[0,2]
            sage: p
            x00*x01 - x01*x02
            sage: P.steenrod_op(p, 0, 1)
            2*x00*x01 - 2*x01*x02
            sage: P.steenrod_op(p, 0, 2)
            0
            sage: P.steenrod_op(p, 1, 1)
            0
                        
        """
        n = self._n
        X = self.variables()
        result = sum(X[i,j]*p.derivative(X[i,j], k) for j in range(0, n))
        if row_symmetry=="permutation" and result:
            deg = self.multidegree(result) 
            deg = tuple(deg) + tuple(0 for i in range(self._inert))
            if list(deg) != sorted(deg, reverse=True):
                s = reverse_sorting_permutation(deg)
                ss = self.row_permutation(s)
                result = act_on_polynomial(result, ss)
        return result
        
    def diagonal_steenrod(self, p, i1, i2, d1, d2):
        """
        Apply the diagonal Steenrod operator of degrees `d_1` in the `i_1` set of variables 
        and `d_2` in the `i_2` set of variables to `p`. 
        The diagonal Steenrod operator for two sets of variables $x_1, x_2, dots, x_n$ 
        and $y_1, y_2, \dots, y_n$ is given by 
        .. MATh:: \sum_i x_i y_i \partial_{x_i}^{i_1+1} \partial_{y_i}^{2_1+1}
        
        EXEMPLES::
            sage: P = DiagonalPolynomialRing(QQ, 3, 4)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]^2*X[1,0]^3 + X[0,1]^3*X[1,1]^2
            sage: p
            x00^2*x10^3 + x01^3*x11^2
            sage: P.diagonal_steenrod(p, 0, 1, 0, 1)
            12*x00^2*x10^2 + 6*x01^3*x11
            sage: P.diagonal_steenrod(p, 0, 1, 1, 1)
            12*x00*x10^2 + 12*x01^2*x11
            sage: P.diagonal_steenrod(p, 0, 1, 2, 1)
            12*x01*x11
            sage: P.diagonal_steenrod(p, 0, 1, 2, 3)
            0

        """
        n = self._n
        x = self.variables()[i1]
        y = self.variables()[i2]
        return sum(x[i]*y[i]*derivative(derivative(p, x[i], d1+1), y[i], d2+1) for i in range(0, n))
            
    @cached_method
    def derivative_input(self, D, j):
        """
        # TODO NICOLAS add documentation
        """
        r = self._r
        X = self.variables()
        res = []
        for i in range(r):
            res.extend([X[i,j],D[i]])
        return res

    def multi_polarization(self, p, D, i2):
        """
        Return the multi polarization `P_{D,i_2}. p` of `p`.

        The multi polarization operator is defined by
        .. MATH:: P_{D,i_2} := \sum_j x_{i_2,j} \partial_{*,j}^D

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 4, 3)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[1,0]^3*X[1,1]^1 + X[2,1]; p
            x00*x10^3*x11 + x21

        Usual polarizations::

            sage: P.multi_polarization(p, [0,2,0],2)
            6*x00*x10*x11*x20
            sage: P.multi_polarization(p, [0,1,0],2)
            3*x00*x10^2*x11*x20 + x00*x10^3*x21

            sage: P.multi_polarization(p, [0,2,0], 0)
            6*x00^2*x10*x11

            sage: P.multi_polarization(p, [0,0,1], 0)
            x01

        Multi polarizations::

            sage: P.multi_polarization(p, [1,2,0], 2)
            6*x10*x11*x20
        """
        n = self._n
        X = self.variables()
        D = tuple(D)
        if i2>=self._r:
            return None
        else:
            result = self.sum(X[i2,j]*p.derivative(*(self.derivative_input(D, j)))
                              for j in range(n))
            return result
        
    def is_highest_weight_vector(self, p, _assert=False):
        """
        # TODO NICOLAS add documentation
        """
        for i2 in range(self._r):
            for i1 in range(i2):
                if self.polarization(p, i2, i1, 1):
                    if _assert:
                        assert False
                    else:
                        return False
        return True

    def test_highest_weight_vector(self, p):
        """
        # TODO NICOLAS add documentation
        """
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

            sage: P.highest_weight_vectors(p, 0, 1)  # not tested NICOLAS
            [-x01*x10 + x00*x11, x00^2 - x01^2]
            sage: P.test_highest_weight_vectors(p, 0, 1)   # not tested NICOLAS

        A random example::

            sage: P = DiagonalPolynomialRing(QQ, 4, 3)
            sage: P.inject_variables()
            Defining x00, x01, x02, x03, x10, x11, x12, x13, x20, x21, x22, x23
            sage: x00, x01, x02, x03, x10, x11, x12, x13, x20, x21, x22, x23 = P._P.gens()
            sage: p = 1/2*x10^2*x11*x20 + 3*x10*x11*x12*x20 + 1/3*x11^2*x12*x20 + 1/2*x10*x11*x12*x21 + x10*x11^2*x22 + 1/15*x10*x11*x12*x22 - 2*x11^2*x12*x22 - 2*x12^3*x22
            sage: res = P.highest_weight_vectors(p)
            sage: res # not tested NICOLAS
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
        """
        # TODO NICOLAS add documentation
        """
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
        # TODO NICOLAS add documentation
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
            sage: e0 = e(R, 0); e1 = e(R, 1)
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

            sage: f0 = f(R, 0)
            sage: f1 = f(R, 1)
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
            sage: e0 = e(R, 0); e1 = e(R, 1)
            sage: R.inject_variables()
            Defining x00, x01, x02, x03, x10, x11, x12, x13, x20, x21, x22, x23
            sage: x00, x01, x02, x03, x10, x11, x12, x13, x20, x21, x22, x23 = R._P.gens()
            sage: p = 1/2*x02*x10*x20 - 1/2*x03*x10*x20 - 5/2*x02*x11*x20 + 5/2*x03*x11*x20 - 3/2*x00*x12*x20 - 1/2*x01*x12*x20 + 2*x02*x12*x20 + 3/2*x00*x13*x20 + 1/2*x01*x13*x20 - 2*x03*x13*x20 - 2*x02*x10*x21 + 2*x03*x10*x21 + 2*x00*x12*x21 - 2*x03*x12*x21 - 2*x00*x13*x21 + 2*x02*x13*x21 - 2*x00*x10*x22 + 1/2*x01*x10*x22 + 3/2*x02*x10*x22 + 5/2*x00*x11*x22 - 5/2*x03*x11*x22 - 1/2*x00*x12*x22 + 1/2*x03*x12*x22 - 1/2*x01*x13*x22 - 3/2*x02*x13*x22 + 2*x03*x13*x22 + 2*x00*x10*x23 - 1/2*x01*x10*x23 - 3/2*x03*x10*x23 - 5/2*x00*x11*x23 + 5/2*x02*x11*x23 + 1/2*x01*x12*x23 - 2*x02*x12*x23 + 3/2*x03*x12*x23 + 1/2*x00*x13*x23 - 1/2*x02*x13*x23

            sage: p = x02*x10*x20 - x00*x12*x20
            sage: R.multidegree(p)
            (1, 1, 1)

            sage: q = x00*x02*x10 - x00^2*x12
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

def reverse_sorting_permutation(t): # TODO: put "stable sorting" as keyword somewhere
    r"""
    Return a permutation `p` such that  is decreasing

    INPUT:
    - `t` -- a list/tuple/... of numbers

    OUTPUT:

    a minimal permutation `p` such that `w \circ p` is sorted decreasingly

    EXAMPLES::

        sage: t = [3, 3, 1, 2]
        sage: s = reverse_sorting_permutation(t); s
        [1, 2, 4, 3]
        sage: [t[s[i]-1] for i in range(len(t))]
        [3, 3, 2, 1]

        sage: t = [4, 2, 3, 2, 1, 3]
        sage: s = reverse_sorting_permutation(t); s
        [1, 3, 6, 2, 4, 5]
        sage: [t[s[i]-1] for i in range(len(t))]
        [4, 3, 3, 2, 2, 1]
    """
    return ~(Word([-i for i in t]).standard_permutation())

def e(P, i):
    """
    # TODO NICOLAS add documentation
    """
    return functools.partial(P.polarization, i1=i, i2=i+1, d=1)

def f(P, i):
    """
    # TODO NICOLAS add documentation
    """
    return functools.partial(P.polarization, i1=i+1, i2=i, d=1)
    
def e_polarization_degrees(D1, D2):
    """
    Return the degree of an e-multipolarization operator from degree D1 to degree D2

    EXAMPLES::

        sage: e_polarization_degrees([5,0,0],[3,1,0])
        (1, [2, 0, 0])
        sage: e_polarization_degrees([5,0,0],[3,1,0])
        (1, [2, 0, 0])
        sage: e_polarization_degrees([5,0,0],[3,2,0])
        sage: e_polarization_degrees([5,1,0],[3,2,0])
        (1, [2, 0, 0])
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


##############################################################################
# Polynomial ring with diagonal action with antisymmetries
##############################################################################

class DiagonalAntisymmetricPolynomialRing(DiagonalPolynomialRing):
    """
    The ring of diagonal antisymmetric polynomials in $n \times r$ variables 
    and $n \times k$ inert variables.

    EXAMPLES::

        sage: P = DiagonalAntisymmetricPolynomialRing(QQ, 4, 3)
        sage: P
        Diagonal antisymmetric polynomial ring with 3 rows of 4 variables over Rational Field

    """
    def __init__(self, R, n, r, inert=0, antisymmetries=None):
        DiagonalPolynomialRing.__init__(self, R, n, r, inert=inert)
        self._antisymmetries = antisymmetries

    def _repr_(self):
        """
        sage: DiagonalAntisymmetricPolynomialRing(QQ, 5, 3)
        Diagonal antisymmetric polynomial ring with 3 rows of 5 variables over Rational Field
        sage: DiagonalAntisymmetricPolynomialRing(QQ, 5, 3, inert=1)
        Diagonal antisymmetric polynomial ring with 3 rows of 5 variables and 1 row(s) of inert variables over Rational Field

        """
        if self._inert == 0 :
            return "Diagonal antisymmetric polynomial ring with %s rows of %s variables over %s"%(self._r, self._n, self.base_ring())
        else :
            return "Diagonal antisymmetric polynomial ring with %s rows of %s variables and %s row(s) of inert variables over %s"%(self._r, self._n, self._inert, self.base_ring())

    def polarization(self, p, i1, i2, d, row_symmetry=None):
        """
        Return the polarization `P_{d,i_1,i_2}. p` of `p`. 
        The result is reduced with respect to the given antisymmetries. 
        
        EXAMPLES::
            sage: mu = Partition([3])
            sage: antisymmetries = antisymmetries_of_tableau(mu.initial_tableau())
            sage: P = DiagonalAntisymmetricPolynomialRing(QQ, 4, 3, antisymmetries = antisymmetries)
            sage: x = P.variables()
            sage: v = -x[0,0]^2*x[0,1] + x[0,0]*x[0,1]^2 + x[0,0]^2*x[0,2] - x[0,1]^2*x[0,2] - x[0,0]*x[0,2]^2 + x[0,1]*x[0,2]^2
            sage: P.polarization(v, 0, 1, 1)
            -2*x00*x01*x10 + x01^2*x10 + 2*x00*x02*x10 - x02^2*x10 - x00^2*x11 + 2*x00*x01*x11 - 2*x01*x02*x11 + x02^2*x11 + x00^2*x12 - x01^2*x12 - 2*x00*x02*x12 + 2*x01*x02*x12

            sage: mu = Partition([2,1])
            sage: antisymmetries = antisymmetries_of_tableau(mu.initial_tableau())
            sage: antisymmetries = tuple(tuple(a) for a in antisymmetries)
            sage: P = DiagonalAntisymmetricPolynomialRing(QQ, 4, 3, antisymmetries = antisymmetries)
            sage: x = P.variables()
            sage: v = -x[0,0]^2*x[0,1] + x[0,0]*x[0,1]^2 + x[0,0]^2*x[0,2] - x[0,1]^2*x[0,2] - x[0,0]*x[0,2]^2 + x[0,1]*x[0,2]^2
            sage: P.polarization(v, 0, 1, 1)
            -4*x00*x01*x10 + 2*x01^2*x10 + 4*x00*x02*x10 - 2*x00^2*x11 + 4*x00*x01*x11 + 2*x00^2*x12

            sage: mu = Partition([1,1,1])
            sage: antisymmetries = antisymmetries_of_tableau(mu.initial_tableau())
            sage: antisymmetries = tuple(tuple(a) for a in antisymmetries)
            sage: P = DiagonalAntisymmetricPolynomialRing(QQ, 4, 3, antisymmetries = antisymmetries)
            sage: x = P.variables()
            sage: v = -x[0,0]^2*x[0,1] + x[0,0]*x[0,1]^2 + x[0,0]^2*x[0,2] - x[0,1]^2*x[0,2] - x[0,0]*x[0,2]^2 + x[0,1]*x[0,2]^2
            sage: P.polarization(v, 0, 1, 1)
            -12*x00*x01*x10 - 6*x00^2*x11
        """
        antisymmetries = self._antisymmetries
        result = super(DiagonalAntisymmetricPolynomialRing,self).polarization(p, i1, i2, d, row_symmetry=row_symmetry)
        if antisymmetries and result:
            result = antisymmetric_normal(result, self._n, self._r+self._inert, antisymmetries)
        return result

    def multi_polarization(self, p, D, i2): 
        """
        Return the multi polarization `P_{D,i_2}. p` of `p`.
        The result is reduced with respect to the given antisymmetries.
        
        EXAMPLES::
            sage: mu = Partition([2,1])
            sage: antisymmetries = antisymmetries_of_tableau(mu.initial_tableau())
            sage: antisymmetries = tuple(tuple(a) for a in antisymmetries)
            sage: P = DiagonalAntisymmetricPolynomialRing(QQ, 4, 3, antisymmetries = antisymmetries)
            sage: x = P.variables()
            sage: v = -x[0,0]^2*x[0,1] + x[0,0]*x[0,1]^2 + x[0,0]^2*x[0,2] - x[0,1]^2*x[0,2] - x[0,0]*x[0,2]^2 + x[0,1]*x[0,2]^2
            sage: P.multi_polarization(v, [1,0,0], 1)
                -2*x00*x01*x10 + x01^2*x10 + 2*x00*x02*x10 - x00^2*x11 + 2*x00*x01*x11 + x00^2*x12
        """
        antisymmetries = self._antisymmetries
        result = super(DiagonalAntisymmetricPolynomialRing,self).multi_polarization(p,D,i2)
        if antisymmetries and result:
            result = reduce_antisymmetric_normal(result, self._n, self._r+self._inert, antisymmetries)
        return result
        
        
    def steenrod_op(self, p, i, k, row_symmetry=None):
        """
        """
        antisymmetries = self._antisymmetries
        result = super(DiagonalAntisymmetricPolynomialRing,self).steenrod_op(p, i, k, row_symmetry=row_symmetry)
        if antisymmetries and result:
            result = antisymmetric_normal(result, self._n, self._r+self._inert, antisymmetries)
        return result
