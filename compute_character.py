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

def vandermonde(gamma, r=0):
    """
    Let `gamma` be a diagram of $n$ cells and $x = (x_1, x_2, \dots, x_n)$ and
    $\theta = (\theta_1, \theta_2, \dots, \theta_n)$ two sets of n variables.
    Then it returns the determinant of the matrix $(x_i^a\theta_i^b)$
    for $1 \leq i \leq n$ and $(a,b) the cells of `mu`.

    INPUT: 
    - ``gamma`` -- A Partition or a Diagram
    
    OUtPUT:
    - An element of a Diagonal Polynomial Ring in `r` rows of variables

    EXAMPLES::
        sage: gamma = Diagram([(0,0),(1,0),(3,0)])
        sage: vandermonde(gamma)
        -x00^3*x01 + x00*x01^3 + x00^3*x02 - x01^3*x02 - x00*x02^3 + x01*x02^3
        sage: v = vandermonde(Partition([2,1]), r=2)
        sage: v
        -x01*theta00 + x02*theta00 + x00*theta01 - x02*theta01 - x00*theta02 + x01*theta02
        sage: v.parent()
        Diagonal Polynomial Ring with 2 rows of 3 variables and inert variables over Rational Field

    """
    n = gamma.size()
    if r == 0:
        r = 1
    P = DiagonalPolynomialRing(QQ, n, r, inert=1) 
    X = P.variables()
    Theta = P.inert_variables()
    return matrix([[x**i[1]*theta**i[0] for i in gamma.cells()] 
                   for x,theta in zip(X[0],Theta[0])]).determinant()

    

##############################################################################
# Operators
##############################################################################

def partial_derivatives(P):
    """
    Return the partial derivative functions in all the variables of `P` allowed
    for derivation (ie not in the inert variables).
    
    INPUT:
    - `P` -- a diagonal polynomial ring
    
    """
    n = P.ncols()
    r = P.nrows()
    D = P.grading_set()
    X = P.derivative_variables()
    op = {}
    for i in range(r):
        op[D((-1 if j==i else 0 for j in range(r)))] = [attrcall("derivative", X[i,k]) for k in range(n)]
    return op

def polarization_operators(r, max_deg=1, side=None, row_symmetry=None):
    """
    Return the polarization operator functions in `r` sets of variables with
    maximum degree `max_deg`.
    
    INPUT:
    - `r` -- an integer
    - `max_deg` -- an integer
    - `row_symmetry` -- "permutation" (only implemented case)
    
    """
    D = cartesian_product([ZZ for i in range(r)])
    return {D([-d if i==i1 else 1 if i==i2 else 0 for i in range(r)]):
            [attrcall("polarization", i1=i1, i2=i2, d=d, row_symmetry=row_symmetry)]
            for d in range(1, max_deg+1)
            for i1 in range(0, r)
            for i2 in range(0, r)
            if (i1<i2 if side == 'down' else i1!=i2)
           }

def steenrod_operators(r, degree=1, row_symmetry=None):
    """
    Return the Steenrod operator functions in `r` sets of variables of 
    degree `degree`.
    
    INPUT:
    - `r` -- a integer
    - `degree` -- an integer
    - `row_symmetry` -- "permutation" (only implemented case)
    
    """
    D = cartesian_product([ZZ for i in range(r)])
    op = {}
    for i in range(r):
        op[D((-degree if j==i else 0 for j in range(r)))] = [
            attrcall("steenrod_op", i=i, k=degree+1, row_symmetry=row_symmetry)]
    return op

def symmetric_derivatives(r, list_deg, row_symmetry=None):
    """
    Return the symmetric derivative functions in `r` sets of variables for the 
    degree listed in `list_deg`.
    
    INPUT:
    - `r` -- a integer
    - `list_deg` -- a list of tuples
    - `row_symmetry` -- "permutation" (only implemented case)
    
    """
    D = cartesian_product([ZZ for i in range(r)])
    return {D(-i for i in d) : [attrcall("symmetric_derivative", d=d, row_symmetry=row_symmetry)] 
            for d in list_deg}
 
##############################################################################
# Utilities
##############################################################################

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

def IsotypicComponent(S, arg, use_antisymmetry=False):
    """
    Project the basis of the given subspace S on the isotypic components of $S_n$
    or on the isotypic component of the given type. 
    
    INPUT:
        -``S`` -- Subspace
        -``arg`` -- an integer or a partition
        
    OUTPUT:
        - A dict of Suspaces, one Subspace for each isotypic component
        
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
    P1 = basis.values().pop()[0].parent()
    for nu in list_partitions:
        result_nu = {}
        if use_antisymmetry == True:
            antisymmetries = antisymmetries_of_tableau(nu.initial_tableau())
            P2 = DiagonalAntisymmetricPolynomialRing(P1._R, P1.ncols(), P1.nrows(), 
                                                 P1.ninert(), antisymmetries)
        for deg, value in basis.iteritems():
            if use_antisymmetry:
                gen = []
                for p in value:
                    temp = apply_young_idempotent(P2(p), nu)
                    if temp != 0: 
                        gen += [temp]
            else:
                gen = []
                for p in value:
                    temp = apply_young_idempotent(p, nu)
                    if temp != 0:
                        gen += [temp]
            if gen != []:
                result_nu[(deg, tuple(nu))] = Subspace(gen, {}).basis()[0]
        if result_nu != {}:
            result[nu] = Subspace(result_nu, operators={})
                
    if len(result.keys()) == 1:
        key = result.keys()[0]
        return result[key]
    else:
        return result


def add_degrees_isotypic(gen_deg, op_deg):
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
    D = cartesian_product([ZZ for i in range(len(gen_deg[0]))])
    return D(gen_deg[0])+D(op_deg), gen_deg[1]
    
def add_degrees_symmetric(gen_deg,op_deg):
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
    D = cartesian_product([ZZ for i in range(len(gen_deg[0]))])
    d = D(gen_deg[0])+D(op_deg)
    return D(sorted(d, reverse=True)), gen_deg[1]
    
    
##############################################################################
# Polarization Space
##############################################################################

def PolarizedSpace(S, operators, add_degrees=add_degrees_isotypic):
    """
    Polarized the subspace S with the given operators on the polynomial ring P. 
    
    INPUT:
    - ``P`` -- a polynomial ring
    - ``S`` -- a subspace
    - ``operators`` -- a list or a dictionnary of operators acting on elements of P
    - ``add_degrees`` -- a function that will be used to determine the degrees of the elements computed
    
    EXAMPLES::
    """
    if isinstance(S, dict):
        return {key : PolarizedSpace(value, operators, add_degrees=add_degrees)
                for key, value in S.iteritems()}
    else:
        basis = S.basis()
        basis_element = basis.values().pop()[0]
        P1 = basis_element.parent()
        r = len(op_pol.keys().pop())
        row_symmetry = op_pol.values().pop()[0].kwds['row_symmetry']
        if row_symmetry == "permutation":
            add_degrees = add_degrees_symmetric
        D = cartesian_product([ZZ for i in range(r)])
        generators = {}

        if isinstance(P1, DiagonalAntisymmetricPolynomialRing):
            P2 = DiagonalAntisymmetricPolynomialRing(P1._R, P1.ncols(), r , P1.ninert(), P1.antisymmetries())
            for key, value in basis.iteritems():
                d = (D((key[0][0] if i==0 else 0 for i in range(0,r))), key[1])
                generators[d] = tuple(reduce_antisymmetric_normal(P2(b), 
                                                      b.parent().ncols(), 
                                                      b.parent().nrows()+b.parent().ninert(), 
                                                      b.antisymmetries()) for b in value)
        else :
            P2 = DiagonalPolynomialRing(P1._R, P1.ncols(), r , P1.ninert())
            for key, value in basis.iteritems():
                d = (D((key[0][0] if i==0 else 0 for i in range(0,r))), key[1])
                generators[d] = tuple(P2(b) for b in value)
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
    if isinstance(S, dict):
        return {key : Range(value, operators, add_degrees=add_degrees)
                for key, value in S.iteritems()}

    result = {}
    basis = S.basis()
    for key, b in basis.iteritems():
        result = merge(result, {add_degrees(key, deg): 
                                     [op(p) for p in b for op in op_list if op(p)!=0] 
                                     for deg, op_list in operators.iteritems()})    
    if result != {} :
        return Subspace(result, {}, add_degrees) #{} <-> operators
    else :
        return None
        
        
##############################################################################
# Character
##############################################################################

def character(S, left_basis=s, right_basis=s, row_symmetry=None):
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
    if isinstance(S, dict):
        return sum(character(V,
                             left_basis=left_basis, right_basis=right_basis, row_symmetry=row_symmetry) 
                   for V in S.values())
    else:
        basis = S.basis()
        basis_element = basis.values().pop()[0]
        P = basis_element.parent()
        n = P.ncols()
        r = P.nrows()
        
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
    """
    Return the factorization of the tensor product `f` w.r.t the right symmetric
    functions. The right symmetric functions have their supports in the partitions
    on `n`. 
    
    INPUT:
    - ``f`` -- a sum of tensor products on symmetric functions
    - ``n`` -- an Integer
    """
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
    """
    Return the dimension of the tensor product `f` w.r.t the right symmetric
    functions. The right symmetric functions have their supports in the partitions
    on `n` and they reprensent characters of `S_n`. 
    
    INPUT:
    - ``f`` -- a sum of tensor products on symmetric functions
    - ``n`` -- an Integer
    """
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


##############################################################################
# Main function
############################################################################## 

def compute_character(mu, use_antisymmetry=True, row_symmetry="permutation"):
    n = Integer(mu.size())
    # Determinant computation
    v = vandermonde(mu)
    # Span by derivatives
    generator = {v.multidegree() : [v]}
    list_op = partial_derivatives(v.parent())
    V = Subspace(generators=generator, operators=list_op, add_degrees=add_degree)
    # Projection on isotypic components
    V_iso = IsotypicComponent(V, n, use_antisymmetry=use_antisymmetry)
    # Polarization
    r = n-1
    deg = v.degree()
    if deg == 0:
        deg = 1
    op_pol = polarization_operators(r, deg, row_symmetry=row_symmetry)
    V_pol = PolarizedSpace(V_iso, op_pol)
    
    # character
    return character(V_pol, row_symmetry=row_symmetry)
