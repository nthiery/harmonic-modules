#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.combinat.sf.sfa import *
load("code.py")
load("diagram.py")

##############################################################################
# Polynomial ring with diagonal action and inert variables
##############################################################################

class DiagonalPolynomialRingInert(DiagonalPolynomialRing):
    
    # r = total number of variables sets 
    # k = number of inert variables sets
    # R = ring (ex: QQ)

    def __init__(self, R, n, r, k=1):
        names = ["x%s%s"%(i,j) for i in range(r) for j in range(n)]
        P = PolynomialRing(R, n*(r), names)
        vars = P.gens()
        self._P = P
        self._R = R
        self._Q = PolynomialRing(QQ,'q',r-k)
        DiagonalPolynomialRing.__init__(self,R,n,r)
        self._grading_set = cartesian_product([ZZ for i in range(r-k)])
        self._k = k
        self._X = matrix([[vars[i*n+j] for j in range(n)] for i in range(r-k)])
        self._Theta = matrix([[vars[i*n+j] for j in range(n)] for i in range(r-k,r)])

    def _repr_(self):
        """
            sage: DiagonalPolynomialRingInert(QQ,3,3)
            Diagonal polynomial ring with 3 rows of 3 variables including 1 row(s) of inert variables over Rational Field

        """
        return "Diagonal polynomial ring with %s rows of %s variables including %s row(s) of inert variables over %s"%(self._r, self._n, self._k, self.base_ring())

    def variables_X(self): 
        """
            EXAMPLES::
                sage: DP = DiagonalPolynomialRingInert(QQ,3,3)
                sage: X = DP.variables_X()
                sage: X

                [x00 x01 x02]
                [x10 x11 x12]

        """
        return self._X
        
    def variables_Theta(self): 
        """
            EXAMPLES::
                sage: DP = DiagonalPolynomialRingInert(QQ,3,3)
                sage: Theta = DP.variables_Theta()
                sage: Theta
                [x20 x21 x22]

        """
        return self._Theta
        
    def multidegree(self,p):
        """
            Return the multidegree of the multihomogeneous polynomial `p`
            
            EXAMPLES::
                sage: DP = DiagonalPolynomialRingInert(QQ,3,3)
                sage: p = DP.vandermonde([3])
                sage: p
                -x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2
                sage: DP.multidegree(p)
                [3, 0, 0]
                sage: q = x11*x20 + x10*x21
                sage: DP.multidegree(q)
                [0, 1, 1]

        """

        n = self._n
        r = self._r
        return [sum(p.exponents()[0][i] for i in range(j*n,(j+1)*n)) for j in range(0,r)]
            
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
        
    def vandermonde(self,mu):
        """
            Let `mu` be a diagram (of a partition or no) and $X=(x_i)$ and 
            $\Theta = (\theta_i)$ two sets of n variables.
            Then $\Delta$ is the determinant of the matrix $(x_i^a\theta_i^b)$ 
            for (a,b) the cells of `mu`.
            
            INPUT: A partition `mu`
            
            OUTPUT: 
                - The determinant Delta
            
            EXAMPLES:: 
                sage: DP.vandermonde([3])
                -x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2
                sage: DP.vandermonde([2,1])
                -x01*x20 + x02*x20 + x00*x21 - x02*x21 - x00*x22 + x01*x22
                sage: DP.vandermonde([1,1,1])
                -x20^2*x21 + x20*x21^2 + x20^2*x22 - x21^2*x22 - x20*x22^2 + x21*x22^2

        """
        X = self._X
        Theta = self._Theta
        if not isinstance(mu,Diagram):
            mu = Diagram(mu)
        Delta = matrix([[x**i[1]*theta**i[0] for i in mu.cells()] for x,theta in zip(X[0],Theta[0])]).determinant()
        return Delta
        
    def dimension_vandermonde(self,mu) :
        return sum([i[1] for i in mu.cells()])
        
    def sym_derivative(self,p,a,b,X,Y):
        """
            Compute the symmetric derivative of the polynomial `p`.
            The symmetric derivative is defined to be a sum of derivatives of degree `a` in the
            variables of `X` and of degree `b` in the variables of `Y`: 
            $\sum_{i=1}^n \frac{\partial^b }{\partial y_i^b} \frac{\partial^a}{\partial x_i^a}$
            
            INPUT:
                - `p` -- a multivariate polynomial
                - `X` and `Y` -- two sets of variables for the derivation
                - `a` and `b` -- integers for the degree of derivation resp. in `X` and `Y`
                
            EXAMPLES::
                sage: X = DP.variables()[0]
                sage: DP.sym_derivative(DP.vandermonde([3]),2,0,X[0],X[1])
                0
                sage: DP.sym_derivative(x00^3+x01^3+x10^2+x12,2,1,X[0],X[1])
                0
                sage: DP.sym_derivative((x00^3+x01^3)*(x10^2+x12),2,1,X[0],X[1])
                12*x00*x10

        """
        return sum(p.derivative(x,a,y,b) for x,y in zip(X,Y))

    def symmetric_derivative_by_degree(self):
        """
            Returns a dictonnary containing all the symmetric derivatives of the form
            $\sum_{i=1}^n \frac{\partial^b }{\partial y_i^b} \frac{\partial^a}{\partial x_i^a}$
            for the non inert variables of `self`, indexed by degree.
            
            EXAMPLES::
                sage: DP.symmetric_derivative_by_degree()

                {-2: [<functools.partial object at 0x7fc33ad13100>],
                 -1: [<functools.partial object at 0x7fc33ad13940>,
                  <functools.partial object at 0x7fc33ad13730>],
                 0: [<functools.partial object at 0x7fc33ad13b50>]}
        """
        rows = self._r - self._k
        X = self._X
        dsym = {}
        for i in range (0,rows):
            for j in range (i+1,rows):
                for i1 in range(0,rows):
                    for i2 in range(0,rows):
                        d = -(i1+i2)
                        if d in iter(dsym): 
                            dsym[d] += [functools.partial(self.sym_derivative, a=i1, b=i2, X=X[i], Y=X[j])]
                        else:
                            dsym[d] = [functools.partial(self.sym_derivative, a=i1, b=i2, X=X[i], Y=X[j])]
        return dsym

    def derivatives_by_degree(self):
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

    def polarizators_by_degree(self):
        """
            Returns a dictonnary containing the polarization operators indexed by degree.
            
            EXAMPLES::
                sage: DP.polarizators_by_degree()

                {-1: [<functools.partial object at 0x7fc33abb5418>,
                  <functools.partial object at 0x7fc33ac0b628>],
                 0: [<functools.partial object at 0x7fc33ad13368>,
                  <functools.partial object at 0x7fc3422068e8>]}
                sage: DP.operators_by_degree(diff=True,pol=True,sym_diff=True)

        """
        pol = self.polarization_operators_by_degree(inert=1)
        res = {}
        for d,op in pol.iteritems(): 
            if sum(d) not in res.keys():
                res[sum(d)] = op
            else:
                res[sum(d)] += op
        return res
        
    def central_projector(self,mu,V): 
        # TODO NOT TESTED
        # projection pour partage mu de l'ensemble V
        n = self._n
        rep = SymmetricGroupRepresentation(mu)
        c = factorial(n)/rep.to_character().values()[0]
        proj = []
        for v in V: 
            cj = dimV/dim * sum(rep.representation_matrix(p).trace()*act(p,v) for p in Permutations(n))
            if cj != 0:
                proj += [cj]
        return proj
        
    @cached_method
    def isotypic_basis(self,mu,use_antisymmetries=False,verbose=True):
        """
            Let $W$ be the smallest submodule generated by a Vandermonde $\Delta$ depending on 
            a partition`mu` and closed under partial derivatives.
            Then $W$ can be decomposed into isotypic components for the action of $S_n$. This function 
            compute the basis of W using the Young idempotents to project on isotypic components.
            
            EXAMPLES::
                sage: DP = DiagonalPolynomialRingInert(QQ,3,3)
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
        if use_antisymmetries:
            for d,B in basis.iteritems():
                pos = antisymmetries_of_tableau(d[1])
                res = [reduce_antisymmetric_normal(p,n,r,pos) for p in B]
                basis[d] = res
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
    
    def character_schur(self,mu,parallel=True): 
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
    return DPRI.character_schur(mu,parallel=parallel)
        
def character_key(mu, **args):
    return tuple(Composition(mu))
def character_hash(mu):
    return str(list(mu)).replace(" ","")[1:-1]
character_with_inert = func_persist(character_with_inert,hash=character_hash,key=character_key)


############################################

def multipower(d,q):
    """
        Return the product of the terms $q_i^{d_i}$.
        
        INPUT:
            - `d` -- a multidegree
            - `q` -- a list of variables on which apply the multidegree
            
        EXAMPLES::
            sage: q = PolynomialRing(QQ,'q',4).gens()
            sage: q
            (q0, q1, q2, q3)
            sage: d = [1,0,2,0]
            sage: multipower(d,q)
            q0*q2^2
            sage: d = [4,3,2,1]
            sage: multipower(d,q)
            q0^4*q1^3*q2^2*q3
    """
    return prod(q[i]**d[i] for i in range(0,len(q)))

def basis_by_component(basis,nu):
    """
        Get all the elements of `basis` whose index contains `nu` and make 
        a dict with these elements indexed by the associated integer.
        
        INPUT:
            - `basis` -- a dict indexed by tuples containing an integer and a partition
            - `nu` -- a partition
            
        EXAMPLES::
            sage: DP = DiagonalPolynomialRingInert(QQ,3,3)
            sage: basis = DP.isotypic_basis(Partition([3]))
            sage: basis

            {(0, [3]): [108],
             (1, [2, 1]): [-18*x00],
             (2, [2, 1]): [-3*x00^2 + 6*x00*x01],
             (3, [1, 1, 1]): [-x00^2*x01]}
            sage: basis_by_component(basis,Partition([3]))
            {0: [108]}
            sage: basis_by_component(basis,Partition([2,1]))
            {1: [-18*x00], 2: [-3*x00^2 + 6*x00*x01]}
            sage: basis_by_component(basis,Partition([1,1,1]))
            {3: [-x00^2*x01]}
            sage: basis_by_component(basis,Partition([1,1]))
            {}
    """
    nu_basis = {}
    for d,B in basis.iteritems():
        if d[1]==nu: 
            nu_basis.update({d[0]:B})
    return nu_basis

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
