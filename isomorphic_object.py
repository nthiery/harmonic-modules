#!/usr/bin/env python
# -*- coding: utf-8 -*-

import functools

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

from diagram import *
from subspace import *
from young_idempotent import *
from polynomial_derivative import *

from utilities import *
from antisymmetric_utilities import *



# Stuff here everything currently missing in SageMath about isomorphic algebras
class Algebras_IsomorphicObjects(IsomorphicObjectsCategory):
    class ParentMethods:
        def summation(self, x, y):
            return self.retract(x.lift() + y.lift())
        def gens(self):
            return [self.retract(g) for g in self.ambient().gens()]

Algebras.IsomorphicObjects = Algebras_IsomorphicObjects

class IsomorphicObject(UniqueRepresentation, Parent):
    def ambient(self):
        return self._ambient
    def lift(self, p):
        return p.value
    def retract(self, p):
        return self.element_class(self,p)
    def base_ring(self):
        return self.ambient().base_ring()
    def __init__(self, ambient, category):
        self._ambient = ambient
        Parent.__init__(self, category=category.IsomorphicObjects())
        # Bricolage
        self._remove_from_coerce_cache(ambient)
        phi = sage.categories.morphism.SetMorphism(Hom(ambient, self, category), self.retract)
        phi.register_as_coercion()

    class Element(ElementWrapper):
        pass
        
        
class DiagonalPolynomialRing(IsomorphicObject):
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
        IsomorphicObject.__init__(self, P, Algebras())
        vars = P.gens()
        self._P = P
        self._R = R
        self._Q = PolynomialRing(QQ,'q',r)
        self._grading_set = cartesian_product([ZZ for i in range(r)])
        self._hilbert_parent = PolynomialRing(ZZ, r, 'q')
        #dans fonctions direct
        self._vars = matrix([[vars[i*n+j] for j in range(n)] for i in range(r+inert)])
        self._X = matrix([[vars[i*n+j] for j in range(n)] for i in range(r)])
        self._Theta = matrix([[vars[i*n+j] for j in range(n)] for i in range(r,r+inert)])
        
        
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
            
    def nrows(self):
        """
        Return the number of sets of variables.
        """
        return self._r
        
    def ncolumns(self):
        """
        Return the number of variables in each set.
        """
        return self._n
        
    def ninert(self):
        """
        Return the number of sets if inert variables.
        """
        return self._inert
    
    def inject_variables(self):
        self._P.inject_variables()

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
        return prod(q[i]**d[i] for i in range(0,len(q))
        
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
        
    class Element(IsomorphicObject.Element):
        def multidegree(self):
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
        n = self.parent().ncolumns()
        r = self.parent().nrows()
        v = self.exponents()[0]
        return self._grading_set([sum(v[n*i+j] for j in range(n))
                                  for i in range(r)])
                                  
        
        def polarization(self, i1, i2, d, row_symmetry=None):
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
        n = self.parent().ncolumns()
        r = self.parent().nrows()
        X = self.parent().variables()
        if i1>=r or i2 >=r:
            print "Row number out of range."
            return None
        else:
            result = sum(X[i2,j]*self.derivative(X[i1,j],d)
                              for j in range(n))
            if row_symmetry=="permutation" and result:
                d = self.multidegree(result)
                d = tuple(d) + tuple(0 for i in range(self._inert))
                if list(d) != sorted(d, reverse=True):
                    s = reverse_sorting_permutation(d)
                    ss = self.row_permutation(s)
                    result = act_on_polynomial(result, ss)
            return result
"""

sage: %runfile isomorphic_object.py
sage: P = PolynomialRing(QQ, ['x','y'])
sage: PP = IsomorphicObject(P, Algebras(QQ))
sage: x,y = PP.gens() 
sage: (2*x + y)^2 + 1
4*x^2 + 4*x*y + y^2 + 1
"""
