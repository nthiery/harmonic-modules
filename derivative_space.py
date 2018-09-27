#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.parallel.decorate import parallel
from sage.combinat.ranker import rank_from_list
from sage.combinat.sf.sf import SymmetricFunctions

from utilities import index_filling
from antisymmetric_utilities import *
from diagonal_polynomial_ring import *
from polynomial_derivative import *
from add_degree import *


####################################################
# Derivative Harmonic Space
####################################################

class DerivativeHarmonicSpace():
    """
    The space generated by the Vandermonde determinant and
    its derivatives.
    
    EXAMPLES::
    
        sage: DerivativeHarmonicSpace(QQ, 4) #not tested
        
    FIXME:: 
        Pourquoi on obtient "<__main__.DerivativeHarmonicSpace instance at ...>"
        a l'initialisation et non "Derivative space generated by..." comme dans DiagonalPolynomialRing?

    """
    def __init__(self, R, n, use_antisymmetry=False):
        self._R = R
        self._n = n
        self._use_antisymmetry = use_antisymmetry
        if use_antisymmetry:
            self._antisymmetries = antisymmetries_of_tableau(Partition([n]).initial_tableau())
            self._polRing = DiagonalAntisymmetricPolynomialRing(R, n, 1, antisymmetries=self._antisymmetries)
        else : 
            
            self._antisymmetries = None
            self._polRing = DiagonalPolynomialRing(R, n, 1)
            
    def _repr_(self):
        """
        
        """
        return "Derivative space generated by the Vandermonde determinant of degree %s and its derivatives"%(self._n)
        
    def basis_by_shape(self, mu):
        """
        Return the elements of the basis of `self` that are in the isotypic component 
        indexed by `mu`. 
        
        EXAMPLES::
            sage: H = DerivativeHarmonicSpace(QQ, 3, use_antisymmetry=True)
            sage: for mu in Partitions(3):
            ....:     print(H.basis_by_shape(mu))
            [6]
            [1/3*x00^2 - 2/3*x00*x01, -2*x00]
            [-x00^2*x01]

        """
        mu = Partition(mu)
        return [self.higher_specht(t, harmonic=True) for t in StandardTableaux(mu)]

    def higher_specht(self, P, Q=None, harmonic=False):
        r"""
        Return the hyper specht polynomial indexed by `P` and `Q` in the first row of variables

        See :func:`higher_specht` for details.

        EXAMPLES::

            sage: R = DerivativeHarmonicSpace(QQ, 3)
            sage: R._polRing.algebra_generators()
            [x00 x01 x02]

            sage: for la in Partitions(3):
            ....:     for P in StandardTableaux(la):
            ....:         print(ascii_art(la, R.higher_specht(P), sep="    "))
            ....:         print
                ***    6
                <built-in function print>
                **    
                *     -x00*x01 + x01*x02
                <built-in function print>
                **    
                *     -2*x00 + 2*x02
                <built-in function print>
                *    
                *    
                *    -x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2
                <built-in function print>

            sage: R = DerivativeHarmonicSpace(QQ, 3, use_antisymmetry=True)
            sage: for la in Partitions(3):
            ....:     for P in StandardTableaux(la):
            ....:         print(ascii_art(la, R.higher_specht(P), sep="    "))
            ....:         print
            ....:
                ***    6
                <built-in function print>
                **    
                *     -x00*x01
                <built-in function print>
                **    
                *     -2*x00
                <built-in function print>
                *    
                *    
                *    -x00^2*x01
                <built-in function print>
        """
        X = self._polRing.algebra_generators()
        # the self._n forces a multivariate polynomial ring even if n=1
        R = PolynomialRing(self._polRing.base_ring(), self._n, list(X[0]))
        H = higher_specht(R, P, Q, harmonic=harmonic, use_antisymmetry=self._use_antisymmetry)
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
        ....:             print(ascii_art(la, P, Q, factor(higher_specht(R, P, Q)), sep="    "))
        ....:             print
            ***      1  2  3      1  2  3    2 * 3
            <built-in function print>
            *       2         2       
            **      1  3      1  3    (-1) * z * (x - y)
            <built-in function print>
            *       2         3       
            **      1  3      1  2    (-1) * y * (x - z)
            <built-in function print>
            *       3         2       
            **      1  2      1  3    (-2) * (x - y)
            <built-in function print>
            *       3         3       
            **      1  2      1  2    (-2) * (x - z)
            <built-in function print>
            *      3      3    
            *      2      2    
            *      1      1    (y - z) * (-x + y) * (x - z)
            <built-in function print>


        sage: factor(higher_specht(R, Partition([2,1])))
        (-2) * (x - z)

        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         print(ascii_art(la, P, factor(higher_specht(R, P)), sep="    "))
        ....:         print
            ***      1  2  3    2 * 3
            <built-in function print>
            *       2       
            **      1  3    (-1) * y * (x - z)
            <built-in function print>
            *       3       
            **      1  2    (-2) * (x - z)
            <built-in function print>
            *      3    
            *      2    
            *      1    (y - z) * (-x + y) * (x - z)
            <built-in function print>


        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         for Q in StandardTableaux(la):
        ....:             print(ascii_art(la, P, Q, factor(higher_specht(R, P, Q, harmonic=True)), sep="    "))
        ....:             print
        ***      1  2  3      1  2  3    2 * 3
        <built-in function print>
        *       2         2
        **      1  3      1  3    (-1/3) * (-x - y + 2*z) * (x - y)
        <built-in function print>
        *       2         3
        **      1  3      1  2    (-1/3) * (-x + 2*y - z) * (x - z)
        <built-in function print>
        *       3         2
        **      1  2      1  3    (-2) * (x - y)
        <built-in function print>
        *       3         3
        **      1  2      1  2    (-2) * (x - z)
        <built-in function print>
        *      3      3
        *      2      2
        *      1      1    (y - z) * (-x + y) * (x - z)
        <built-in function print>

        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         for Q in StandardTableaux(la):
        ....:             print(ascii_art(la, P, Q, factor(higher_specht(R, P, Q, harmonic="dual")), sep="    "))
        ....:             print
        ***      1  2  3      1  2  3    2^2 * 3
        <built-in function print>
        *       2         2
        **      1  3      1  3    (-2) * (-x^2 - 2*x*y + 2*y^2 + 4*x*z - 2*y*z - z^2)
        <built-in function print>
        *       2         3
        **      1  3      1  2    (-2) * (x^2 - 4*x*y + y^2 + 2*x*z + 2*y*z - 2*z^2)
        <built-in function print>
        *       3         2
        **      1  2      1  3    (-2) * (-x + 2*y - z)
        <built-in function print>
        *       3         3
        **      1  2      1  2    (-2) * (x + y - 2*z)
        <built-in function print>
        *      3      3
        *      2      2
        *      1      1    (6) * (y - z) * (-x + y) * (x - z)
        <built-in function print>

    This caught two bugs::

        sage: R = DerivativeHarmonicSpace(QQ, 6)
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


class DerivativeVandermondeSpaceWithInert(UniqueRepresentation):
    """
        The space generated by a generalized version of the Vandermonde determinant 
        containing inert variables with respect to the derivation and its derivatives.
        
        Let $W$ be the smallest submodule generated by the Vandermonde determinant
        $\Delta$ associated to the partition `mu` and closed under partial derivatives.
        
        If `mu` is a diagram which is not a partition, `use_antisymmetry` should be False.
        
        EXAMPLES::

            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [2,1])
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
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [3])
            sage: W.vandermonde()
            -x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [2,1])
            sage: W.vandermonde()
            -x01*theta00 + x02*theta00 + x00*theta01 - x02*theta01 - x00*theta02 + x01*theta02
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [1,1,1])
            sage: W.vandermonde()
            -theta00^2*theta01 + theta00*theta01^2 + theta00^2*theta02 - theta01^2*theta02 - theta00*theta02^2 + theta01*theta02^2
        """
        n = self._n
        mu = self._mu
        X = self._polRing.variables()
        Theta = self._polRing.inert_variables()
        #if not isinstance(mu,Diagram):
            #mu = Diagram(mu)
        Delta = matrix([[x**i[1]*theta**i[0] for i in mu.cells()] for x,theta in zip(X[0],Theta[0])]).determinant()
        return Delta

    def degree_vandermonde(self):
        """
        Return the degree of the Vandermonde determinant associated to `self`
        w.r.t the `x` variables. The `theta` variables are considered to be of degree 0.
        
        EXAMPLES::
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [3])
            sage: W.degree_vandermonde()
            3
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [2,1])
            sage: W.degree_vandermonde()
            1
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [1,1,1])
            sage: W.degree_vandermonde()
            0
        """
        mu = self._mu
        #if not isinstance(mu,Diagram):
            #mu = Diagram(mu)
        return sum([i[1] for i in mu.cells()])
            
    @cached_method
    def basis(self, verbose=False):
        """
        The submodule $W$ can be decomposed into isotypic components 
        for the action of $S_n$. This method compute the basis of W 
        using the Young idempotents to project on isotypic components.

        EXAMPLES::
           sage: W = DerivativeVandermondeSpaceWithInert(QQ, [3])
            sage: W.basis()
            {(0, [3]): [1],
             (1, [2, 1]): [x00 - x02],
             (2, [2, 1]): [x00^2 - 2*x00*x01 + 2*x01*x02 - x02^2],
             (3,
              [1, 1, 1]): [-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2]}
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [2,1])
            sage: W.basis()
            {(0, [2, 1]): [-theta00 + theta02],
             (1, [1, 1, 1]): [x01*theta00 - x00*theta01 + x00*theta02 - x01*theta02]}
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [1,1,1])
            sage: W.basis()
            {(0,
              [1, 1, 1]): [-theta00^2*theta01 + theta00*theta01^2 + theta00^2*theta02 - theta01^2*theta02 - theta00*theta02^2 + theta01*theta02^2]}
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [3], use_antisymmetry=False)
            sage: W.basis()
            {(0, [3]): (1,),
             (1, [2, 1]): (x00 - x02,),
             (2, [2, 1]): (x00^2 - 2*x00*x01 + 2*x01*x02 - x02^2,),
             (3,
              [1, 1, 1]): (-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2,)}
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [2,1], use_antisymmetry=False)
            sage: W.basis()
            {(0, [2, 1]): (-theta00 + theta02,),
             (1,
              [1, 1, 1]): (x01*theta00 - x02*theta00 - x00*theta01 + x02*theta01 + x00*theta02 - x01*theta02,)}

        """
        n = self._n
        mu = self._mu
        X = self._polRing.variables()
        Delta = self.vandermonde()
        dim = self.degree_vandermonde()
        operators = {}
        for nu in Partitions(n):
            operators[(-1,nu)] = [make_deriv_comp_young(X[0][i],nu) for i in range(0,n)]
        F = Subspace(generators={(dim,Partition([1 for i in range(n)])):[Delta]},operators=operators,
                                    add_degrees=add_degree_isotyp, verbose=verbose)
        basis = F.basis()
        if self._use_antisymmetry :
            pos = antisymmetries_of_tableau(Partition(mu).initial_tableau())
            for d,B in basis.iteritems():
                res = [reduce_antisymmetric_normal(p,n,1,pos) for p in B]
                basis[d] = res
        return basis
    
    @cached_method    
    def basis_by_shape(self, nu, verbose=False):
        """
        Return the elements of the basis of `self` contained in the isotypic
        component associated to `nu`. 
        
        INPUT :: `nu` -- a partition
        
        EXAMPLES::
            sage: W = DerivativeVandermondeSpaceWithInert(QQ, [2,1])
            sage: W.basis()
            {(0, [2, 1]): [-theta00 + theta02],
             (1, [1, 1, 1]): [x01*theta00 - x00*theta01 + x00*theta02 - x01*theta02]}
            sage: W.basis_by_shape(Partition([2,1]))
            {(0, [2, 1]): [-theta00 + theta02]}
            sage: W.basis_by_shape(Partition([1,1,1]))
            {(1, [1, 1, 1]): [x01*theta00 - x00*theta01 + x00*theta02 - x01*theta02]}
            sage: W.basis_by_shape(Partition([3]))
            {}

        """
        basis = self.basis(verbose=verbose)
        result = {}
        for d,b in basis.iteritems():
            if nu in d:
                result[d] = b
        return result
