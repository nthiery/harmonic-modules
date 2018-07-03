#!/usr/bin/env python
# -*- coding: utf-8 -*-

import functools
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from funcpersist import *
from diagram import *
from subspace import *

import pyximport
pyximport.install()
from antisymmetric_utilities import *

##############################################################################
# Polynomial ring with diagonal action
##############################################################################

class DiagonalPolynomialRing(UniqueRepresentation, Parent):
    """

     The ring of diagonal polynomials in n x r variables + n inert variables

    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ, 4, 3)
        sage: 
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
        self._Q = PolynomialRing(QQ,'q',r-inert)
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

        """
        if self._inert == 0 :
            return "Diagonal polynomial ring with %s rows of %s variables over %s"%(self._r, self._n, self.base_ring())
        else :
            return "Diagonal polynomial ring with %s rows of %s variables and %s row(s) of inert variables over %s"%(self._r, self._n, self._inert, self.base_ring())

    def base_ring(self):
        return self._P.base_ring()
        
    def monomial(self, *args):
        return self._P.monomial(*args)

    def algebra_generators(self):
        return self._vars
        
    def variables_X(self): #classic_variables ?
        """
            EXAMPLES::
                sage: DP = DiagonalPolynomialRingInert(QQ,3,3)
                sage: X = DP.variables_X()
                sage: X

                [x00 x01 x02]
                [x10 x11 x12]

        """
        return self._X
        
    def variables_Theta(self): #inert_variables ?
        """
            EXAMPLES::
                sage: DP = DiagonalPolynomialRingInert(QQ,3,3)
                sage: Theta = DP.variables_Theta()
                sage: Theta
                [x20 x21 x22]

        """
        if self._inert != 0 :
            return self._Theta
        else : 
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
        X = self.variables_X()
        Theta = self.variables_Theta()
        if not isinstance(mu,Diagram):
            mu = Diagram(mu)
        Delta = matrix([[x**i[1]*theta**i[0] for i in mu.cells()] for x,theta in zip(X[0],Theta[0])]).determinant()
        return Delta
        
    def dimension_vandermonde(self,mu) :
        return sum([i[1] for i in mu.cells()])

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

        OUTPUT:

        a permutation of the variables, as a permutation of `\{1,\ldots,nr\}`

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

    def polarization(self, p, i1, i2, d, use_symmetry=False):
        """
        Return the polarization `P_{d,i_1,i_2}. p` of `p`.

        Recall that the polarization operator is defined by

        .. MATH:: P_{d,i_1,i_2} := \sum_j x_{i_2,j} \partial_{i_1,j}^d

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 4, 3)
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
    
    def polarization_operators_by_multidegree(self, side=None, use_symmetry=False, min_degree=0):
        """
        Return the collection of polarization operators acting on harmonic polynomials

        INPUT:

        - ``side`` -- 'down'
        - ``min_degree`` -- a non negative integer `d` (default: `0`)

          if `d>0`, only return the polarization operators of differential degree `>=d`.

        If ``side`` is `down` (the only implemented choice), only
        the operators from `X_{i1}` to `X_{i2}` for `i1<i2` are returned.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 4, 2)
            sage: ops = P.polarization_operators_by_degree(); ops
            {(-1, 1): [<functools.partial object at ...>],
             (1, -1): [<functools.partial object at ...>],
             (-2, 1): [<functools.partial object at ...>],
             (-3, 1): [<functools.partial object at ...>],
             (1, -3): [<functools.partial object at ...>],
             (1, -2): [<functools.partial object at ...>]}

            sage: P.polarization_operators_by_degree(side="down")
            {(-3, 1): [<functools.partial object at ...>],
             (-1, 1): [<functools.partial object at ...>],
             (-2, 1): [<functools.partial object at ...>]}

            sage: P = DiagonalPolynomialRing(QQ, 3, 3)
            sage: P.polarization_operators_by_degree(side="down")
            {(-1, 1, 0): [<functools.partial object at ...>],
             (-2, 1, 0): [<functools.partial object at ...>],
             (-2, 0, 1): [<functools.partial object at ...>],
             (0, -2, 1): [<functools.partial object at ...>],
             (-1, 0, 1): [<functools.partial object at ...>],
             (0, -1, 1): [<functools.partial object at ...>]}

            sage: P.polarization_operators_by_degree(use_lie=True) # not tested (features disabled)
            {(-2, 1, 0): [<functools.partial object at ...>],
             (-2, 0, 1): [<functools.partial object at ...>],
             (0, 1, -1): [<functools.partial object at ...>],
             (0, -2, 1): [<functools.partial object at ...>],
             (1, -1, 0): [<functools.partial object at ...>]}

            sage: P = DiagonalPolynomialRing(QQ, 4, 3)
            sage: ops = P.polarization_operators_by_degree()
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[1,0]^3*X[1,1]^1 + X[2,1]; p
            x00*x10^3*x11 + x21
            sage: ops[(1,-2,0)][0](p)
            6*x00^2*x10*x11
            sage: ops[(0,-1,1)][0](p)
            3*x00*x10^2*x11*x20 + x00*x10^3*x21
        """
        n = self._n
        r = self._r
        grading_set = self._grading_set
        return {grading_set([-d if i==i1 else 1 if i==i2 else 0 for i in range(r)]):
                [functools.partial(self.polarization, i1=i1, i2=i2, d=d, use_symmetry=use_symmetry)]
                for d in range(min_degree+1, n)
                for i1 in range(0,r)
                for i2 in range(0, r)
                #if ((i1==i2+1 if d==1 else i1<i2) if use_lie else i1<i2 if side == 'down' else i1!=i2)
                if (i1<i2 if side == 'down' else i1!=i2)
               }
               
    def polarization_operators_by_degree(self,side=None, use_symmetry=False, min_degree=0):
        pol = self.polarization_operators_by_multidegree(side=side,use_symmetry=use_symmetry,min_degree=min_degree)
        res = {}
        for d,op in pol.iteritems(): 
            if sum(d) not in res.keys():
                res[sum(d)] = op
            else:
                res[sum(d)] += op
        return res
        
    def derivatives_by_degree(self): #useless ? 
        """
            Returns a dictonnary containing the derivative operators. 
            
            EXAMPLES::
                sage: DP.derivatives_by_degree()

                {-1: [*.derivative(x00),
                  *.derivative(x10),
                  *.derivative(x01),
                  *.derivative(x11),
                  *.derivative(x02),
                  *.derivative(x12)]}

        """
        X = self._X
        n = self._n
        return {-1:[attrcall("derivative", x[i]) for i in range(0,n) for x in X]}

    def add_degree(self, d1,d2):
        d = d1 + d2
        if not all(i>=0 for i in d):
            raise ValueError("invalid degree")
        return d

    def add_degree_symmetric(self, d1,d2):
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
        X = self._X
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
        return basis

    @parallel()
    def character_isotypic(self,nu,basis):
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
            basis_nu = basis_by_component(basis,nu)
            charac = 0
            S = Subspace(generators={d:B for d,B in basis_nu.iteritems()},operators=self.polarizators_by_degree())
            for b in S.basis().values():
                charac += sum(multipower(self.multidegree(p),self._Q.gens()) for p in b)
            return charac
       
    def character_q(self,mu,verbose=True):
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
        n = self._n
        s = SymmetricFunctions(self._Q).s()
        charac = 0
        if not isinstance(mu,Diagram):
            mu = Diagram(mu)
        if mu.size() != n:
            print "Given partition doesn't have the right size."
        else:
            basis = self.isotypic_basis(mu)
            for nu in Partitions(n): 
                charac += self.character_isotypic(nu,basis)*s(nu)
            return charac
        
    def character_q_parallel(self,mu,verbose=True): 
        """
            Computes the character and returns the result as a sum of tensor products
            of polynomials in q variables for the action of $GL_r$ and Schur functions
            for the action of $S_n$ using parallel computation.
            
            INPUT: `mu` a partition
            
            EXAMPLES::
                sage: DP.character_q_parallel(Partition([1,1,1]))
                s[1, 1, 1]
                sage: DP.character_q_parallel(Partition([2,1]))
                (q0+q1)*s[1, 1, 1] + s[2, 1]
                sage: DP.character_q_parallel(Partition([3]))
                (q0^3+q0^2*q1+q0*q1^2+q1^3+q0^2+2*q0*q1+q1^2)*s[1, 1, 1] + (q0^2+q0*q1+q1^2+q0+q1)*s[2, 1] + s[3]

        """
        n = self._n
        s = SymmetricFunctions(self._Q).s()
        charac = 0
        if not isinstance(mu,Diagram):
            mu = Diagram(mu)
        if mu.size() != n:
            print "Given partition doesn't have the right size."
        else:
            basis = self.isotypic_basis(mu)
            for (((nu,_),_),res) in self.character_isotypic([(nu,basis) for nu in Partitions(n)]):
                #print "nu : ",nu
                #print "res : ",res
                charac += res*s(nu)
            return charac
        
    def into_schur(self,charac):
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
        nb_rows = self._n - self._k
        s = SymmetricFunctions(self._Q).s()
        ss = SymmetricFunctions(QQ).s()
        sym_char = 0
        for supp in charac.support():
            if charac.coefficient(supp)==1:
                sym_char += tensor([s[0],s[supp]])
            else:
                sym_char += tensor([s(ss.from_polynomial(self._Q(charac.coefficient(supp))))
                                    .restrict_partition_lengths(nb_rows,exact=False),s[supp]])
        return sym_char
    
    def character_schur(self,mu,parallel=True,verbose=True): 
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
        
        if parallel:
            return self.into_schur(self.character_q_parallel(mu))
        else:
            return self.into_schur(self.character_q(mu))
        

 
##############################################################################
# Harmonic Polynomial ring
##############################################################################

class DiagonalHarmonicPolynomialRing(DiagonalPolynomialRing):
    """

        The ring of diagonal hamonic polynomials in n x r variables.
        
        EXAMPLES::
        
            sage: P = DiagonalHarmonicPolynomialRing(QQ, 4, 3)
            sage: 
    """
    
    def __init__(self, R, n, r, antisymmetric=False):
        DiagonalPolynomialRing.__init__(self, R, n, r, inert=0)
        self._antisymmetric = antisymmetric
        
    def _repr_(self):
        """

        """
        return "Diagonal harmonic polynomial ring with %s rows of %s variables over %s"%(self._r, self._n, self.base_ring())
        
    def harmonic_space_by_shape(self, mu, verbose=False, use_symmetry=False, use_antisymmetry=False, use_lie=False, use_commutativity=False):
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

        if use_antisymmetry:
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

        operators = self.polarization_operators_by_degree(side='down',
                                                          use_symmetry=use_symmetry,
                                                          antisymmetries=antisymmetries,
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
                #print "rejected: %s"% new_word
                return None
            #print new_word
            return new_word
        # print operators
        add_degree = self._add_degree_symmetric if use_symmetry else self._add_degree
        F = Subspace(generators, operators=operators,
                     add_degrees=add_degree, degree=self.multidegree,
                     hilbert_parent = hilbert_parent,
                     extend_word=extend_word, verbose=verbose)
        F._antisymmetries = antisymmetries
        return F

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

        


##############################################################################
# Polynomial ring with diagonal action with antisymmetries
##############################################################################

class DiagonalAntisymmetricPolynomialRing(DiagonalPolynomialRing):
    """

    The ring of diagonal polynomials in n x r variables + n inert variables
    with antisymmetries

    EXAMPLES::

        sage: P = DiagonalAntisymmetricPolynomialRing(QQ, 4, 3)
        sage: 
    """
    def __init__(self, R, n, r, inert=0):
        DiagonalPolynomialRing.__init__(self, R, n, r, inert=inert)

    def _repr_(self):
        """

        """
        if self._inert == 0 :
            return "Diagonal antisymmetric polynomial ring with %s rows of %s variables over %s"%(self._r, self._n, self.base_ring())
        else :
            return "Diagonal antisymmetric polynomial ring with %s rows of %s variables and %s row(s) of inert variables over %s"%(self._r, self._n, self._inert, self.base_ring())


    def polarization(self, p, i1, i2, d, use_symmetry=False, antisymmetries=None):
        """
        
        """
        result = self.polarization(p, i1, i2, d, use_symmetry=use_symmetry)
        if antisymmetries and result:
            result = antisymmetric_normal(result, self._n, self._r, antisymmetries)
        return result

    def multi_polarization(self, p, D, i2, antisymmetries=None):
        """
        
        """
        result = self.multi_polarization(p, D, i2)
        if antisymmetries and result:
            result = antisymmetric_normal(result, self._n, self._r, antisymmetries)
        return result

    
    def polarization_operators_by_multidegree(self, side=None, use_symmetry=False, antisymmetries=None, min_degree=0):
        """
    
        """
        n = self._n
        r = self._r
        grading_set = self._grading_set
        return {grading_set([-d if i==i1 else 1 if i==i2 else 0 for i in range(r)]):
                [functools.partial(self.polarization_antisym, i1=i1, i2=i2, d=d, use_symmetry=use_symmetry,antisymmetries=antisymmetries)]
                for d in range(min_degree+1, n)
                for i1 in range(0,r)
                for i2 in range(0, r)
                if (i1<i2 if side == 'down' else i1!=i2)
               }
               
    def polarization_operators_by_degree(self,side=None, use_symmetry=False, antisymmetries=None, min_degree=0):
        pol = self.polarization_operators_by_multidegree_antisym(side=side,use_symmetry=use_symmetry,antisymmetries=antisymmetries,min_degree=min_degree)
        res = {}
        for d,op in pol.iteritems(): 
            if sum(d) not in res.keys():
                res[sum(d)] = op
            else:
                res[sum(d)] += op
        return res
    
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
        basis = self.isotypic_basis(mu,verbose=verbose)
        for d,B in basis.iteritems():
                pos = antisymmetries_of_tableau(d[1])
                res = [reduce_antisymmetric_normal(p,n,r,pos) for p in B]
                basis[d] = res
        return basis


##############################################################################
# Young idempotent
##############################################################################


def apply_young_idempotent(p, t, use_antisymmetry=False):
    """
    Apply the Young idempotent indexed by `t` on the polynomial `p`

    INPUT::

    - `t` -- a standard tableau or a partition
    - `p` -- a polynomial on as many variables as there are cells in `t`

    The Young idempotent first symmetrizes `p` according to the
    row stabilizer of `t` and then antisymmetrizes the result according
    to the column stabilizer of `t` (a cell containing `i` in `t`
    being associated to the `i`-th variable (starting at `i=1`)
    of the polynomial ring containing `p`.

    .. TODO:: normalize result

    EXAMPLES::

        sage: x,y,z = QQ['x,y,z'].gens()
        sage: p = x^2 * y
        sage: t = StandardTableau([[1],[2],[3]])
        sage: apply_young_idempotent(p, t)
        x^2*y - x*y^2 - x^2*z + y^2*z + x*z^2 - y*z^2

        sage: apply_young_idempotent(p, Partition([1,1,1]))
        x^2*y - x*y^2 - x^2*z + y^2*z + x*z^2 - y*z^2

        sage: t = StandardTableau([[1,2,3]])
        sage: apply_young_idempotent(p, t)
        x^2*y + x*y^2 + x^2*z + y^2*z + x*z^2 + y*z^2

        sage: apply_young_idempotent(p, Partition([3]))
        x^2*y + x*y^2 + x^2*z + y^2*z + x*z^2 + y*z^2

        sage: t = StandardTableau([[1,2],[3]])
        sage: p = x*y*y^2
        sage: apply_young_idempotent(p, t)
        x^3*y + x*y^3 - y^3*z - y*z^3

        sage: p = x*y*z^2
        sage: apply_young_idempotent(p, t)
        -2*x^2*y*z + 2*x*y*z^2
    """
    if isinstance(t, Partition):
        t = t.initial_tableau()
    p = sum(act(Permutation(sigma),p) for sigma in t.row_stabilizer() )
    if use_antisymmetry:
        antisymmetries = antisymmetries_of_tableau(t)
        p = antisymmetric_normal(p, t.size(), 1, antisymmetries)
    else:
        p = sum(sigma.sign()*act(Permutation(sigma),p) for sigma in t.column_stabilizer() )
    return p

def act(sigma,v) :
    """
    Return sigma(v).

    INPUT:

    - `sigma` -- a permutation
    - `v` -- a polynomial 

    """
    
    X = v.parent().gens()
    r = len(X)/len(sigma)
    n = len(sigma)
    sub = {}
    for j in range(0,r) :
        sub.update({X[i+n*j]:X[sigma[i]-1+n*j] for i in range (0,n) if i!=sigma[i]-1})
    return v.subs(sub)
        
def make_deriv_comp_young(x,mu):
    """
        Return a function which corresponds to a partial derivative in `x`
        composed with the young idempotent for the partition `mu`.
        
        INPUT: 
            - `x` -- a variable for the derivation
            - `mu` -- a partition
        
        EXAMPLES::
        sage: P = DiagonalPolynomialRing(QQ,3,3)
        sage: X = P.algebra_generators()
        sage: [make_deriv_comp_young(x,mu) for x in X[0] for mu in Partitions(3)]

        [<function f at 0x7f7f64111f50>,
         <function f at 0x7f7f64111140>,
         <function f at 0x7f7f64111938>,
         <function f at 0x7f7f64111320>,
         <function f at 0x7f7f64111398>,
         <function f at 0x7f7f641115f0>,
         <function f at 0x7f7f641155f0>,
         <function f at 0x7f7f64115668>,
         <function f at 0x7f7f64115578>]

    """
    def f(p): 
        return apply_young_idempotent(derivative(p,x),mu)
    return f

