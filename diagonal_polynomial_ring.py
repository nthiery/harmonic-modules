#!/usr/bin/env python
# -*- coding: utf-8 -*-

import functools
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.sage_object import load
from sage.parallel.decorate import parallel
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

from funcpersist import *
from diagram import *
from subspace import *
from young_idempotent import *

import antisymmetric_utilities

##############################################################################
# Polynomial ring with diagonal action
##############################################################################

class DiagonalPolynomialRing(UniqueRepresentation, Parent):
    """

    The ring of diagonal polynomials in n x r variables and n x k inert variables

    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ, 4, 3)
        sage: P
        Diagonal polynomial ring with 3 rows of 4 variables over Rational Field

        sage: P = DiagonalPolynomialRing(QQ,4,3,inert=1)
        sage: P
        Diagonal polynomial ring with 3 rows of 4 variables and 1 row(s) of inert variables over Rational Field

    """
    def __init__(self, R, n, r, inert=0):
        names = ["x%s%s"%(i,j) for i in range(r+inert) for j in range(n)]
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
            sage: DiagonalPolynomialRing(QQ, 5, 3) # indirect doctest
            Diagonal polynomial ring with 3 rows of 5 variables over Rational Field
            sage: DiagonalPolynomialRing(QQ,4,3,inert=1) # indirect doctest
            Diagonal polynomial ring with 3 rows of 4 variables and 1 row(s) of inert variables over Rational Field

        """
        if self._inert == 0 :
            return "Diagonal polynomial ring with %s rows of %s variables over %s"%(self._r, self._n, self.base_ring())
        else :
            return "Diagonal polynomial ring with %s rows of %s variables and %s row(s) of inert variables over %s"%(self._r, self._n, self._inert, self.base_ring())

    def base_ring(self):
        """
            sage: D = DiagonalPolynomialRing(QQ,4,3)
            sage: D.base_ring()
            Rational Field

        """
        return self._P.base_ring()
        
    def polynomial_ring(self):
        """
            sage: D = DiagonalPolynomialRing(QQ,4,3,inert=1)
            sage: D.polynomial_ring()
            Multivariate Polynomial Ring in q0, q1, q2 over Rational Field

        """
        return self._Q

    def algebra_generators(self):
        """
            Return all the variables, the classic ones and the inert ones. 
            
            EXAMPLES ::
            
                sage: D = DiagonalPolynomialRing(QQ,4,3,inert=1)
                sage: D
                Diagonal polynomial ring with 3 rows of 4 variables and 1 row(s) of inert variables over Rational Field
                sage: D.algebra_generators()
                [x00 x01 x02 x03]
                [x10 x11 x12 x13]
                [x20 x21 x22 x23]
                [x30 x31 x32 x33]
                
                sage: D = DiagonalPolynomialRing(QQ,4,3)
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
                sage: DP = DiagonalPolynomialRing(QQ,3,3,inert=1)
                sage: DP.variables()
                [x00 x01 x02]
                [x10 x11 x12]
                [x20 x21 x22]
                
        """
        return self._X

    def inert_variables(self):
        """
            Return only the inert variables. 
            
            EXAMPLES::
                sage: DP = DiagonalPolynomialRing(QQ,3,3,inert=1)
                sage: DP.inert_variables()
                [x30 x31 x32]

                sage: DP = DiagonalPolynomialRing(QQ,3,3)
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
        The inert variables are of degree 0.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,3,2)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[0,1]^2 * X[1,0]^2*X[1,1]^3
            sage: P.multidegree(p)
            (3, 5)
            sage: P.multidegree(P.zero())
            -1
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

    def polarization(self, p, i1, i2, d, use_symmetry=False):
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

            sage: P.polarization(p, 1, 0, 2)
            6*x00^2*x10*x11

            sage: P.polarization(p, 2, 0, 1)
            x01
        """
        n = self._n
        X = self.algebra_generators()
        result = self.sum(X[i2,j]*p.derivative(X[i1,j],d)
                          for j in range(n))
        if use_symmetry and result:
            d = self.multidegree(result)
            if list(d) != sorted(d, reverse=True):
                s = reverse_sorting_permutation(d)
                ss = self.row_permutation(s)
                result = act_on_polynomial(result, ss)
        return result

    @cached_method
    def derivative_input(self, D, j): 
        r = self._r
        X = self.algebra_generators()
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
        X = self.algebra_generators()
        D = tuple(D)
        result = self.sum(X[i2,j]*p.derivative(*(self.derivative_input(D, j)))
                          for j in range(n))
        return result


##############################################################################
# Polynomial ring with diagonal action with antisymmetries
##############################################################################

class DiagonalAntisymmetricPolynomialRing(DiagonalPolynomialRing):
    """

    The ring of diagonal polynomials in n x r variables + n inert variables
    with antisymmetries

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

        """
        if self._inert == 0 :
            return "Diagonal antisymmetric polynomial ring with %s rows of %s variables over %s"%(self._r, self._n, self.base_ring())
        else :
            return "Diagonal antisymmetric polynomial ring with %s rows of %s variables and %s row(s) of inert variables over %s"%(self._r, self._n, self._inert, self.base_ring())

    def polarization(self, p, i1, i2, d, use_symmetry=False):
        #TODO : trouver exemples pertinents pour cette fonction 
        """
            EXAMPLES::
            
                sage: P = DiagonalAntisymmetricPolynomialRing(QQ,4,3)
                sage: X = P.algebra_generators()
                sage: p = X[0,0]*X[1,0]^3*X[1,1]^1 + X[2,1]; p
                x00*x10^3*x11 + x21
                sage: P.polarization(p,0,1,1)
                x10^4*x11
                sage: P.polarization(p,1,0,1)
                x00*x01*x10^3 + 3*x00^2*x10^2*x11


        """
        antisymmetries = self._antisymmetries
        result = super(DiagonalAntisymmetricPolynomialRing,self).polarization(p,i1,i2,d,use_symmetry=use_symmetry)
        if antisymmetries and result:
            result = antisymmetric_normal(result, self._n, self._r, antisymmetries)
        return result

    def multi_polarization(self, p, D, i2):
        #TODO : trouver exemples pertinents pour cette fonction 
        """

        """
        antisymmetries = self._antisymmetries
        result = super(DiagonalAntisymmetricPolynomialRing,self).multi_polarization(p,D,i2)
        if antisymmetries and result:
            result = antisymmetric_normal(result, self._n, self._r, antisymmetries)
        return result

