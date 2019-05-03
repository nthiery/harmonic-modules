#!/usr/bin/env python
# -*- coding: utf-8 -*-

from diagonal_polynomial_ring import*
from subspace import*
from young_idempotent import*
from add_degree import*
from diagram import*

SymmetricFunctions(QQ).inject_shorthands(verbose=False)


##############################################################################
# Vandermonde like determinant
##############################################################################

def vandermonde(gamma):
    """
    Let `gamma` be a diagram of $n$ cells and $x = (x_1, x_2, \dots, x_n)$ and
    $\theta = (\theta_1, \theta_2, \dots, \theta_n)$ two sets of n variables.
    Then it returns the determinant of the matrix $(x_i^a\theta_i^b)$
    for $1 \leq i \leq n$ and $(a,b) the cells of `mu`.

    INPUT: 
    - ``gamma`` -- A Partition or a Diagram

    EXAMPLES::
        sage: gamma = Diagram([(0,0),(1,0),(3,0)])
        sage: vandermonde(gamma)
        -x00^3*x01 + x00*x01^3 + x00^3*x02 - x01^3*x02 - x00*x02^3 + x01*x02^3
        sage: vandermonde(Partition([2,1]))
        -x01*theta00 + x02*theta00 + x00*theta01 - x02*theta01 - x00*theta02 + x01*theta02
    """
    n = gamma.size()
    P = DiagonalPolynomialRing(QQ, n, 1, inert=1)
    X = P.variables()
    Theta = P.inert_variables()
    return matrix([[x**i[1]*theta**i[0] for i in gamma.cells()] 
                   for x,theta in zip(X[0],Theta[0])]).determinant()

def degree_vandermonde(gamma):
    """
    Returns the degree in $x$ of the vandermonde determinant computer
    from `gamma`. 

    INPUT: 
    - ``gamma`` -- A Partition or a Diagram

    EXAMPLES::
        sage: gamma = Diagram([(0,0),(1,0),(3,0)])
        sage: degree_vandermonde(gamma)
        4
        sage: degree_vandermonde(Partition([2,1]))
        1
    """
    return sum([i[1] for i in gamma.cells()])
    

##############################################################################
# Operators
##############################################################################

def deriv(x, k=1):
    """
    Return a function that computes the k-th derivative in variable `x`. 
    """
    def f(p):
        return derivative(p, x, k)
    return f

def partial_derivatives(P):
    """
    Return a list of all the partial derivatives functions (of degree 1)
    in the variable of P.
    
    INPUT: 
    - ``P`` -- a polynomial ring.
    """
    n = P._n
    r = P._r
    D = P._grading_set
    X = P.variables()
    op = {}
    for i in range(r):
        op[D((-1 if j==i else 0 for j in range(r)))] = [deriv(X[i,k]) for k in range(n)]
    return op

def steenrod_operators(P, degree=1):
    """
    Return a list of the steenrod operators of a given degree in the variables
    of the polynomial ring P. 
    
    The Steenrod operator of degree `k` in the `x` variables is defined as follow. 
    MATH..:: \sum_i x_i \partial_{x_i}^{k+1}
    
    INPUT: 
    - ``P`` -- a polynomial ring
    - ``degree`` -- an Interger. 
    """
    r = P._r
    D = P._grading_set
    op = {}
    for i in range(r):
        op[D((-degree if j==i else 0 for j in range(r)))] = [functools.partial(P.steenrod_op, i=i, k=degree+1)]
    return op

def polarization_operators(P, side=None, row_symmetry=None, max_deg=0):
    """
    Return the list of all the polarisation operators in the variables of P
    as functions. 
    
    The polarisation operators in the variables `x` and `y` are given by 
    MATH..:: \sum_i y_i partial_{x_i}^k 
    If the parameter side is equal to 'None' only the operators going from a set 
    of variables `x_i` to a set `x_j` with `i leq j` are created. A maximum degree
    can be specify. The degree of an operator is defined to be `k-1`. 
    
    INPUT : 
    - ``P`` -- a polynomial ring in at least 2 sets of variables
    - ``side`` -- must be set at `down` if only upper operators are wanted
    - ``row_symmetry`` -- only implemented case `permutation`
    - ``max_degree`` -- maximum degree of the operators
    """
    n = P._n
    r = P._r
    D = P._grading_set
    if max_deg==0:
        max_deg=n
    return {D([-d if i==i1 else 1 if i==i2 else 0 for i in range(r)]):
            [functools.partial(P.polarization, i1=i1, i2=i2, d=d, row_symmetry=row_symmetry)]
            for d in range(1, max_deg+1)
            for i1 in range(0, r)
            for i2 in range(0, r)
            if (i1<i2 if side == 'down' else i1!=i2)
           }

def higher_polarization_operators(P, side=None, row_symmetry=None, max_deg=0):
    """
    Return the higher polarization operators in the sets of variables of `P`. 
    
    Those operators are given by
    MATH..:: \sum_i x_i y_i \dots \partial_{x_i}^{k_1} \partial_{y_i}^{k_2} \dots
    
    INPUT:
    - ``P`` - a polynomial ring in at least two sets of variables
    - ``side`` -- must be set at `down` if only upper operators are wanted
    - ``row_symmetry`` -- only implemented case `permutation`
    - ``max_degree`` -- maximum degree of the operators
    """
    n = P._n
    r = P._r
    D = P._grading_set
    if max_deg==0:
        max_deg=n
    return {D([-d1 if i==i1 else d2 if i==i2 else 0 for i in range(r)]):
            [functools.partial(P.higher_polarization, i1=i1, i2=i2, d1=d1, d2=d2, row_symmetry=row_symmetry)]
            for d1 in range(1, max_deg+1)
            for d2 in range(1, 3)
            for i1 in range(0, r)
            for i2 in range(0, r)
            if (i1<i2 if side == 'down' else i1!=i2)
           }


def symmetric_derivatives(P, list_deg, row_symmetry=None):
    """
    Return the list of all symmetric derivative of degree contained
    in `list_degree` in the variables of `P`. 
    
    The symmetric derivatives are given by taking the power sum symmetric
    functions and replacing the variables by the corresponding partial
    derivative. 
    """
    D = P._grading_set
    return {D(-i for i in d) : [functools.partial(P.symmetric_derivative, d=d, row_symmetry=row_symmetry)] 
            for d in list_deg}
  

def merge(dict1, dict2):
    """
    Merge two dictionnaries whose values are lists into the first one. 
    
    INPUT:
    - ``dict1``, ``dict2`` -- dictionnaries
    
    EXAMPLES::
        sage: dict1 = {"colors":["red", "blue"], "numbers":[1,2,3]}
        sage: dict2 = {"colors":["blue", "green"]}
        sage: merge(dict1, dict2)
        {'colors': ['red', 'blue', 'blue', 'green'], 'numbers': [1, 2, 3]}

    """
    result = dict1
    for key, value in dict2.iteritems():
        if key in result:
            result[key] += value
        else:
            result[key] = value
    return result

def antisymmetries(mu):
    """
    Return the antisymmetries associated to the canonical stantard tableau
    of the given partition. 
    
    INPUT:
    - ``mu`` -- a Partition
    
    EXAMPLES ::
        sage: antisymmetries(Partition([2,1]))
        ((0, 2), (1,))
        sage: antisymmetries(Partition([3]))
        ((0,), (1,), (2,))
        sage: antisymmetries(Partition([4,2,1,1]))
        ((0, 4, 6, 7), (1, 5), (2,), (3,))

    """
    mu = Partition(mu)
    return antisymmetries_of_tableau(mu.initial_tableau())
    
##############################################################################
# Projection on isotypic components
##############################################################################

def Isotyp(S, arg):
    """
    Project the basis of the given subspace S on the isotypic components of $S_n$
    or on the isotypic component of the given type. 
    
    INPUT:
        -``S`` -- Subspace
        -``arg`` -- an integer or a partition
        
    EXAMPLES::
    
    """
    if isinstance(arg, Partition):
        list_partitions = [arg]
    elif isinstance(arg, Integer):
        list_partitions = Partitions(arg)
    else : 
        print("Error: arg should be a partition or an integer.")
    
    basis = S.basis()
    result = {}
    for nu in list_partitions:
        for key, value in basis.iteritems():
            gen = [apply_young_idempotent(p, nu) for p in value]
            basis_nu = Subspace(gen, {}).basis()
            if basis_nu != {} :
                result[(key, tuple(nu))] = basis_nu[0]
    return Subspace(result, operators={})


def add_degrees_isotypic(d1, d2):
    """
    Compute the sum componentwise of the lists of integrers contained in d1 and d2 
    and return a grading set and the partition contained in d2 as result.
    
    INPUT:
        - ``d1`` -- list containing a list of integers and a partition
        - ``d2`` -- list of integers

    EXAMPLES::
        sage: d1 = ([3,0],[2,1])
        sage: d2 = [-1,0]
        sage: add_degrees_isotypic(d1,d2)
        ((2, 0), [2, 1])

    """
    D = cartesian_product([ZZ for i in range(len(d1[0]))])
    return D(d1[0])s+D(d2), d1[1]
    
def add_degrees_symmetric(d1,d2):
    """
    Compute the sum componentwise of the lists of integrers contained in d1 and d2 
    and return an ordered grading set and the partition contained in d2 as result.
    
    INPUT:
        - ``d1`` -- list containing a list of integers and a partition
        - ``d2`` -- list of integers

    EXAMPLES::
        sage: d1 = ([0, 3],[2,1])
        sage: d2 = [0, -1]
        sage: add_degrees_symmetric(d1,d2)
        ((2, 0), [2, 1])

    """
    D = cartesian_product([ZZ for i in range(len(d1[0]))])
    d = D(d1[0])+D(d2)
    return D(sorted(d, reverse=True)), d1[1]
    
    
##############################################################################
# Polarization Space
##############################################################################

def PolarizedSpace(P, S, operators, add_degrees=add_degrees_isotypic):
    """
    Polarized the subspace S with the given operators on the polynomial ring P. 
    
    INPUT:
    - ``P`` -- a polynomial ring
    - ``S`` -- a subspace
    - ``operators`` -- a list or a dictionnary of operators acting on elements of P
    - ``add_degrees`` -- a function that will be used to determine the degrees of the elements computed
    
    EXAMPLES::
    """
    basis = S.basis()
    n = P._n
    r = P._r
    inert = P._inert
    D = P._grading_set
    generators = {}
    
    if isinstance(P, DiagonalAntisymmetricPolynomialRing):
        antisymmetries = P._antisymmetries
        for key, value in basis.iteritems():
            d = (D((key[0][0] if i==0 else 0 for i in range(0,r))), key[1])
            generators[d] = [antisymmetric_normal(P(b), n, r+inert, antisymmetries) for b in value]
    else :
        for key, value in basis.iteritems():
            d = (D((key[0][0] if i==0 else 0 for i in range(0,r))), key[1])
            generators[d] = [P(b) for b in value]
            
    return Subspace(generators, operators, add_degrees=add_degrees)  
    
##############################################################################
# Quotient
##############################################################################

def Range(S, operators, add_degrees=add_degrees_isotypic):
    """
    Return the image of the basis of the subspace S by the given operators. 
    
    INPUT:
    - ``S`` -- a subspace
    - ``operators`` -- a list or a dictionnary of operators acting on elements of P
    - ``add_degrees`` -- a function that will be used to determine the degrees of the elements computed
    
    EXAMPLES::
    """
    result = {}
    basis = S.basis()
    for key, b in basis.iteritems():
        result = merge(result, {add_degrees(key, deg): 
                                     [op(p) for p in b for op in op_list if op(p)!=0] 
                                     for deg, op_list in operators.iteritems()})    
    if result != {} :
        return Subspace(result, {}, add_degrees)
    else :
        return None
        
        
##############################################################################
# Character
##############################################################################

def character(S, n, r, left_basis=s, right_basis=s, row_symmetry=None):
    """
    Return the bicharacter of the subspace `S` into the given bases. The subspace `S`
    must be a multivariate polynomial subspace on `r` sets of `n` variables. 
    
    INPUT:
    - ``S`` -- a subspace
    - ``n``, ``r`` -- integers
    - ``left_basis`` -- a basis of the symmetric functions for the $GL_r$-character
    - ``right_basis`` -- a basis of the symmetric functions for the $S_n$-character
    - ``row_symmetry`` -- use "permutation" to compute using the symmetries on rows
    
    EXAMPLES::
    """
    basis = S.basis()
    charac = 0
    if row_symmetry != "permutation":
        q = PolynomialRing(QQ,'q',r).gens()
        
    for nu in Partitions(n):
        basis_nu = {}
        charac_nu = 0
        # Get the nu_isotypic part of the basis
        for key, value in basis.iteritems():
            if Partition(key[1]) == nu:
                basis_nu[key[0]] = value
        
        # Use monomials to compute the character
        if row_symmetry == "permutation":
            for deg, b in basis_nu.iteritems():
                charac_nu += sum(m(Partition(deg)) for p in b)
            if charac_nu != 0 :
                if left_basis == s :
                    charac_nu = s(charac_nu).restrict_partition_lengths(r,exact=False)
                elif left_basis != m :
                    charac_nu = left_basis(charac_nu)
                
        # Or use directly the degrees
        else:
            for deg, b in basis_nu.iteritems():
                charac_nu += sum(prod(q[i]**deg[i] for i in range(0,len(deg))) for p in b)
            if charac_nu != 0 :
                if left_basis == s :
                    charac_nu = s.from_polynomial(charac_nu).restrict_partition_lengths(r,exact=False)           
                else:
                    charac_nu = left_basis.from_polynomial(charac_nu)
                
        # Make the tensor product with s[nu]
        if charac_nu != 0:
            charac += tensor([charac_nu, right_basis(s(nu))])
    return charac
    
    
def character_quotient(M, N, n, r, left_basis=s, right_basis=s):
    """
    Compute the difference of bicharacter between the subspaces `M` and `N`.
    They have to be subspaces of multivariate polynomials on `r` sets of `n` variables. 
    
    INPUT:
    - ``M``, ``N`` -- subspaces
    - ``n``, ``r`` -- integers
    - ``left_basis`` -- a basis of the symmetric functions for the $GL_r$-character
    - ``right_basis`` -- a basis of the symmetric functions for the $S_n$-character
    - ``row_symmetry`` -- use "permutation" to compute using the symmetries on rows
    
    EXAMPLES::
    """
    b_tot = M.basis()
    b_ideal = N.basis()
    charac = 0
    q = PolynomialRing(QQ,'q',r).gens()
    
    for nu in Partitions(n):
        basis_nu_tot = {}
        basis_nu_ideal = {}
        charac_nu = 0
        # Get the nu_isotypic part of the bases
        for key, value in b_tot.iteritems():
            if Partition(key[1]) == nu:
                basis_nu_tot[key[0]] = value
        for key, value in b_ideal.iteritems():
            if Partition(key[1]) == nu:
                basis_nu_ideal[key[0]] = value
                
        # Use the degrees to compute the character
        for deg, b in basis_nu_tot.iteritems():
            charac_nu += sum(prod(q[i]**deg[i] for i in range(0,len(deg))) for p in b)
        for deg, b in basis_nu_ideal.iteritems():
            charac_nu -= sum(prod(q[i]**deg[i] for i in range(0,len(deg))) for p in b)
        if charac_nu != 0 :
            if left_basis == s :
                charac_nu = s.from_polynomial(charac_nu).restrict_partition_lengths(r,exact=False)           
            else:
                charac_nu = left_basis.from_polynomial(charac_nu)      
            # Make the tensor product with s[nu]
            charac += tensor([charac_nu, right_basis(s(nu))])
            
    return charac
    
    
##############################################################################
# Tools on character
##############################################################################      

def factorise(f, n):
    SymmetricFunctions(QQ).s()
    supp = sorted(f.support())
    result = {}
    res = []
    for mu in Partitions(n):
        result[mu] = []
        for (a, b), c in zip(supp, f.coefficients()):
            if b == mu :
                result[mu] += [(a,c)]
    result2 = [(mu,sum(c*s(nu) for (nu,c) in result[mu])) for mu in result.keys()]
    for a, b in result2:
        if b!=0:
            print a
            show(b)
        
def dimension(f, n):
    supp = sorted(f.support())
    result = {}
    res = []
    for mu in Partitions(n):
        result[mu] = []
        for (a, b), c in zip(supp, f.coefficients()):
            if b == mu :
                result[mu] += [(a,c)]
    result2 = [(mu,sum(c*s(nu) for (nu,c) in result[mu]).expand(1, alphabet=['q'])) for mu in result.keys()]
    q = result2[0][1].parent().gens()[0]
    return [(tuple(a), b.subs({q:1})) for a,b in result2]

