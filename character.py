#!/usr/bin/env python
# -*- coding: utf-8 -*-

from pypersist import persist
from sage.misc.misc import attrcall
from sage.categories.tensor import tensor
from sage.misc.latex import latex


from diagonal_polynomial_ring import*
from subspace import*
from young_idempotent import*
from add_degree import*
from diagram import*

from sage.combinat.sf.sf import SymmetricFunctions
m = SymmetricFunctions(QQ).m()
s = SymmetricFunctions(QQ).s()
SymmetricFunctions(QQ).inject_shorthands(verbose=False)
# Workaround #25491 which prevents early unpickling of tensor products
# of symmetric functions
from sage.categories.hopf_algebras_with_basis import HopfAlgebrasWithBasis
HopfAlgebrasWithBasis.TensorProducts

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
    
    OUTPUT:
    - An element of a Diagonal Polynomial Ring in `r` rows of `n` variables

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
    if isinstance(gamma, Integer):
        gamma = Partition([gamma])
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
    
    EXAMPLES::
        sage: P = DiagonalPolynomialRing(QQ, 3, 1)
        sage: partial_derivatives(P)
        {(-1,): [*.derivative(x00), *.derivative(x01), *.derivative(x02)]}
        sage: P = DiagonalPolynomialRing(QQ, 3, 2)
        sage: partial_derivatives(P)
        {(-1, 0): [*.derivative(x00), *.derivative(x01), *.derivative(x02)],
         (0, -1): [*.derivative(x10), *.derivative(x11), *.derivative(x12)]}
        sage: P = DiagonalPolynomialRing(QQ, 3, 1, inert=1)
        sage: partial_derivatives(P)
        {(-1,): [*.derivative(x00), *.derivative(x01), *.derivative(x02)]}

        sage: v = vandermonde(Partition([2,1]))
        sage: gen = {v.multidegree() : [v]}
        sage: op = partial_derivatives(v.parent())
        sage: Subspace(gen, op).basis()
        {(0,): (theta01 - theta02, theta00 - theta02),
         (1,): (x01*theta00 - x02*theta00 - x00*theta01 + x02*theta01 + x00*theta02 - x01*theta02,)}

    """
    n = P.ncols()
    r = P.nrows()
    D = P.grading_set()
    X = P.multivar_pol_ring_variables()
    op = {}
    for i in range(r):
        op[D((-1 if j==i else 0 for j in range(r)))] = [attrcall("derivative", X[i,k]) for k in range(n)]
    return op

def polarization_operators(r, max_deg=1, side=None, row_symmetry=None):
    """
    Return the polarization operator functions in `r` sets of variables with
    maximum degree `max_deg`.
    The polarization operator $P_{x,y}^k$ in defined by 
    $$P_{x,y}^k := \sum_i y_i \partial_{x_i}^k$$
    where X and y are two sets of variables and $\partial_{x_i}^k$ stand for 
    the $k$-th partial derivative in $x_i$.
    The option `side` allows to specify keywork "down" to return only polarization
    operators $P_{x_i,x_j}^k$ such that $i<j$. 
    
    INPUT:
    - `r` -- an integer
    - `max_deg` -- an integer
    - `row_symmetry` -- "permutation" (only implemented case)
    
    EXAMPLES::
        sage: polarization_operators(2)
        {(-1, 1): [*.polarization(i1=0, row_symmetry=None, i2=1, d=1)],
         (1, -1): [*.polarization(i1=1, row_symmetry=None, i2=0, d=1)]}
        sage: polarization_operators(2, max_deg=3)
        {(-3, 1): [*.polarization(i1=0, row_symmetry=None, i2=1, d=3)],
         (-2, 1): [*.polarization(i1=0, row_symmetry=None, i2=1, d=2)],
         (-1, 1): [*.polarization(i1=0, row_symmetry=None, i2=1, d=1)],
         (1, -3): [*.polarization(i1=1, row_symmetry=None, i2=0, d=3)],
         (1, -2): [*.polarization(i1=1, row_symmetry=None, i2=0, d=2)],
         (1, -1): [*.polarization(i1=1, row_symmetry=None, i2=0, d=1)]}
        sage: polarization_operators(2, max_deg=3, side="down")
        {(-3, 1): [*.polarization(i1=0, row_symmetry=None, i2=1, d=3)],
         (-2, 1): [*.polarization(i1=0, row_symmetry=None, i2=1, d=2)],
         (-1, 1): [*.polarization(i1=0, row_symmetry=None, i2=1, d=1)]}

        sage: v = vandermonde(Partition([2,1]), 2)
        sage: gen = {v.multidegree() : [v]}
        sage: op = partial_derivatives(v.parent())
        sage: S = Subspace(gen, op)
        sage: polarizators = polarization_operators(2, max_deg=v.degree())
        sage: Subspace(S.basis(), polarizators).basis()
        {(0, 0): (-theta00 + theta01, -theta00 + theta02),
         (0, 1): (-x11*theta00 + x12*theta00 + x10*theta01 - x12*theta01 - x10*theta02 + x11*theta02,),
         (1, 0): (x01*theta00 - x02*theta00 - x00*theta01 + x02*theta01 + x00*theta02 - x01*theta02,)}
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
    The Steenrod operator $S_{x}^k$ in defined for $k>1$ by 
    $$S_{x}^k := \sum_i x_i \partial_{x_i}^k$$
    where X and y are two sets of variables and $\partial_{x_i}^k$ stand for 
    the $k$-th partial derivative in $x_i$.
    
    INPUT:
    - `r` -- a integer
    - `degree` -- an integer
    - `row_symmetry` -- "permutation" (only implemented case)
    
    EXAMPLES ::
        sage: steenrod_operators(2)
        {(-1, 0): [*.steenrod_op(i=0, row_symmetry=None, k=2)],
         (0, -1): [*.steenrod_op(i=1, row_symmetry=None, k=2)]}
        sage: steenrod_operators(2, 2)
        {(-2, 0): [*.steenrod_op(i=0, row_symmetry=None, k=3)],
         (0, -2): [*.steenrod_op(i=1, row_symmetry=None, k=3)]}

        sage: v = vandermonde(Diagram([(0,0),(1,0),(3,0)]))
        sage: v
        -x00^3*x01 + x00*x01^3 + x00^3*x02 - x01^3*x02 - x00*x02^3 + x01*x02^3
        sage: gen = {v.multidegree() : [v]}
        sage: op = merge(steenrod_operators(1,1), steenrod_operators(1,2))
        sage: Subspace(gen, op).basis()
        {(3,): (-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2,),
         (4,): (-x00^3*x01 + x00*x01^3 + x00^3*x02 - x01^3*x02 - x00*x02^3 + x01*x02^3,)}

    """
    if degree < 1:
        degree = 1
    D = cartesian_product([ZZ for i in range(r)])
    op = {}
    for i in range(r):
        op[D((-degree if j==i else 0 for j in range(r)))] = [
            attrcall("steenrod_op", i=i, k=degree+1, row_symmetry=row_symmetry)]
    return op

def symmetric_derivatives(list_deg, row_symmetry=None):
    """
    Return the symmetric derivative functions for the 
    degree listed in `list_deg`.
    
    INPUT:
    - `r` -- a integer
    - `list_deg` -- a list of tuples
    - `row_symmetry` -- "permutation" (only implemented case)
    
    EXAMPLES::
        sage: list_deg = [(i,j) for i in range(3) for j in range(3) if i+j>0]
        sage: list_deg
        [(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]
        sage: symmetric_derivatives(list_deg)
        {(-2, -2): [*.symmetric_derivative(row_symmetry=None, d=(2, 2))],
         (-2, -1): [*.symmetric_derivative(row_symmetry=None, d=(2, 1))],
         (-2, 0): [*.symmetric_derivative(row_symmetry=None, d=(2, 0))],
         (-1, -2): [*.symmetric_derivative(row_symmetry=None, d=(1, 2))],
         (-1, -1): [*.symmetric_derivative(row_symmetry=None, d=(1, 1))],
         (-1, 0): [*.symmetric_derivative(row_symmetry=None, d=(1, 0))],
         (0, -2): [*.symmetric_derivative(row_symmetry=None, d=(0, 2))],
         (0, -1): [*.symmetric_derivative(row_symmetry=None, d=(0, 1))]}
    """
    r = len(list_deg[0])
    D = cartesian_product([ZZ for i in range(r)])
    return {D(-i for i in d) : [attrcall("symmetric_derivative", d=d, row_symmetry=row_symmetry)] 
            for d in list_deg}

def multipolarization(r, list_deg, i2, row_symmetry=None):
    """
    """
    D = cartesian_product([ZZ for i in range(r)])
    op = {}
    for deg in list_deg:
        op[D(-deg[i]+1 if i==i2 else -deg[i] for i in range(len(deg)))] = [
            attrcall("multi_polarization", D=deg, i2=i2, row_symmetry=row_symmetry)]
    return op
 
##############################################################################
# Merge dictionnaries
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
    for key, value in dict2.items():
        if key in result:
            result[key] += value
        else:
            result[key] = value
    return result
    
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
        sage: v = vandermonde(Partition([3]))
        sage: gen = {v.multidegree() : [v]}
        sage: gen
        {(3,): [-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2]}
        sage: deriv = partial_derivatives(v.parent())
        sage: S = Subspace(gen, deriv)
        sage: S.basis()
        {(0,): (1,),
         (1,): (x00 - x02, x01 - x02),
         (2,): (x00^2 - 2*x00*x01 + 2*x01*x02 - x02^2,
          -2*x00*x01 + x01^2 + 2*x00*x02 - x02^2),
         (3,): (-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2,)}
        sage: V = IsotypicComponent(S, 3)
        sage: for value in V.values():
        ....:     print(value.basis())
        {((3,), (1, 1, 1)): (-x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2,)}
        {((0,), (3,)): (1,)}
        {((2,), (2, 1)): (x00^2 - 2*x00*x01 + 2*x01*x02 - x02^2,), ((1,), (2, 1)): (x00 - x02,)}
        
        sage: V = IsotypicComponent(S, 3, use_antisymmetry=True)
        sage: for value in V.values():
        ....:     print(value.basis())
        {((3,), (1, 1, 1)): (x00^2*x01,)}
        {((0,), (3,)): (1,)}
        {((2,), (2, 1)): (x00^2 - 2*x00*x01,), ((1,), (2, 1)): (x00,)}

    """
    if isinstance(arg, Partition):
        list_partitions = [arg]
    elif isinstance(arg, Integer):
        list_partitions = Partitions(arg)
    else : 
        print("Error: arg should be a partition or an integer.")
    
    basis = S.basis()
    result = {}
    P1 = list(basis.values()).pop()[0].parent()
    for nu in list_partitions:
        result_nu = {}
        if use_antisymmetry == True:
            antisymmetries = antisymmetries_of_tableau(nu.initial_tableau())
            P2 = DiagonalAntisymmetricPolynomialRing(P1._R, P1.ncols(), P1.nrows(), 
                                                 P1.ninert(), antisymmetries)
        for deg, value in basis.items():
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
        key = list(result.keys())[0]
        return result[key]
    else:
        return result
    
##############################################################################
# Polarization Space
##############################################################################

def PolarizedSpace(S, operators, add_degrees=add_degrees_isotypic):
    """
    Polarize the subspace S with the given operators on the polynomial ring P. 
    
    INPUT:
    - ``P`` -- a polynomial ring
    - ``S`` -- a subspace
    - ``operators`` -- a list or a dictionnary of operators acting on elements of P
    - ``add_degrees`` -- a function that will be used to determine the degrees of the elements computed
    
    EXAMPLES::
        sage: v = vandermonde(Partition([3]))
        sage: gen = {v.multidegree() : [v]}
        sage: deriv = partial_derivatives(v.parent())
        sage: S = Subspace(gen, deriv)
        sage: V = IsotypicComponent(S, 3)
        sage: polarizators = polarization_operators(2, max_deg=v.degree())
        sage: P = PolarizedSpace(V, polarizators)
        sage: for value in P.values():
        ....:     print(value.basis())
        {((2, 1), (1, 1, 1)): (-x00*x01*x10 + 1/2*x01^2*x10 + x00*x02*x10 - 1/2*x02^2*x10 - 1/2*x00^2*x11 + x00*x01*x11 - x01*x02*x11 + 1/2*x02^2*x11 + 1/2*x00^2*x12 - 1/2*x01^2*x12 - x00*x02*x12 + x01*x02*x12,), ((1, 1), (1, 1, 1)): (-x01*x10 + x02*x10 + x00*x11 - x02*x11 - x00*x12 + x01*x12,), ((3, 0), (1, 1, 1)): (x00^2*x01 - x00*x01^2 - x00^2*x02 + x01^2*x02 + x00*x02^2 - x01*x02^2,), ((1, 2), (1, 1, 1)): (-1/2*x01*x10^2 + 1/2*x02*x10^2 - x00*x10*x11 + x01*x10*x11 + 1/2*x00*x11^2 - 1/2*x02*x11^2 + x00*x10*x12 - x02*x10*x12 - x01*x11*x12 + x02*x11*x12 - 1/2*x00*x12^2 + 1/2*x01*x12^2,), ((0, 3), (1, 1, 1)): (x10^2*x11 - x10*x11^2 - x10^2*x12 + x11^2*x12 + x10*x12^2 - x11*x12^2,)}
        {((0, 0), (3,)): (1,)}
        {((1, 1), (2, 1)): (x00*x10 - x01*x10 - x00*x11 + x02*x11 + x01*x12 - x02*x12,), ((0, 1), (2, 1)): (x10 - x12,), ((1, 0), (2, 1)): (x00 - x02,), ((0, 2), (2, 1)): (1/2*x10^2 - x10*x11 + x11*x12 - 1/2*x12^2,), ((2, 0), (2, 1)): (-1/2*x00^2 + x00*x01 - x01*x02 + 1/2*x02^2,)}

        
        sage: V = IsotypicComponent(S, 3, use_antisymmetry=True)
        sage: P = PolarizedSpace(V, polarizators)
        sage: for value in P.values():
        ....:     print(value.basis())
        {((2, 1), (1, 1, 1)): (x00*x01*x10 + 1/2*x00^2*x11,), ((1, 1), (1, 1, 1)): (x00*x11,), ((3, 0), (1, 1, 1)): (x00^2*x01,), ((1, 2), (1, 1, 1)): (x00*x10*x11 - 1/2*x00*x11^2,), ((0, 3), (1, 1, 1)): (x10^2*x11,)}
        {((0, 0), (3,)): (1,)}
        {((1, 1), (2, 1)): (x00*x10 - x01*x10 - x00*x11,), ((0, 1), (2, 1)): (x10,), ((1, 0), (2, 1)): (x00,), ((0, 2), (2, 1)): (-1/2*x10^2 + x10*x11,), ((2, 0), (2, 1)): (-1/2*x00^2 + x00*x01,)}


        sage: v = vandermonde(Partition([2,1]))
        sage: gen = {v.multidegree(): [v]}
        sage: deriv = partial_derivatives(v.parent())
        sage: S = Subspace(gen, deriv)
        sage: V = IsotypicComponent(S, 3, use_antisymmetry=True)
        sage: polarizators = polarization_operators(2, max_deg=v.degree())
        sage: P = PolarizedSpace(V, polarizators)
        sage: for value in P.values():
        ....:     print(value.basis())
        {((0, 1), (1, 1, 1)): (x10*theta01,), ((1, 0), (1, 1, 1)): (x00*theta01,)}
        {((0, 0), (2, 1)): (theta00,)}
        
        sage: polarizators = polarization_operators(2, max_deg=v.degree(), row_symmetry="permutation")
        sage: P = PolarizedSpace(V, polarizators)
        sage: for value in P.values():
        ....:     print(value.basis())
        {((1, 0), (1, 1, 1)): (x00*theta01,)}
        {((0, 0), (2, 1)): (theta00,)}

    """
    if isinstance(S, dict):
        return {key : PolarizedSpace(value, operators, add_degrees=add_degrees)
                for key, value in S.items()}
    else:
        basis = S.basis()
        basis_element = list(basis.values()).pop()[0]
        P1 = basis_element.parent()
        if operators != {}:
            r = len(list(operators.keys()).pop())
            row_symmetry = list(operators.values()).pop()[0].kwds['row_symmetry']
        else:
            r=1
            row_symmetry = None
        if row_symmetry == "permutation":
            add_degrees = add_degrees_symmetric
        D = cartesian_product([ZZ for i in range(r)])
        generators = {}

        if isinstance(P1, DiagonalAntisymmetricPolynomialRing):
            P2 = DiagonalAntisymmetricPolynomialRing(P1._R, P1.ncols(), r , P1.ninert(), P1.antisymmetries())
            for key, value in basis.items():
                d = (D((key[0][0] if i==0 else 0 for i in range(0,r))), key[1])
                generators[d] = tuple(reduce_antisymmetric_normal(P2(b), 
                                                      b.parent().ncols(), 
                                                      b.parent().nrows()+b.parent().ninert(), 
                                                      b.antisymmetries()) for b in value)
        else :
            P2 = DiagonalPolynomialRing(P1._R, P1.ncols(), r , P1.ninert())
            for key, value in basis.items():
                if isinstance(key[0], Integer):
                    d = (D((key[0] if i==0 else 0 for i in range(0,r))))
                    add_degrees = add_degree
                else:
                    d = (D((key[0][0] if i==0 else 0 for i in range(0,r))), key[1])
                generators[d] = tuple(P2(b) for b in value)
        return Subspace(generators, operators, add_degrees=add_degrees)
    
##############################################################################
# Quotient
##############################################################################

def Range(S, operators, add_degrees=add_degrees_isotypic):
    """
    Return the basis of the image of the subspace S by the given operators. 
    
    INPUT:
    - ``S`` -- a subspace
    - ``operators`` -- a list or a dictionnary of operators acting on elements of P
    - ``add_degrees`` -- a function that will be used to determine the degrees of the elements computed
    
    EXAMPLES::
    """
    if isinstance(S, dict):
        return {key : Range(value, operators, add_degrees=add_degrees)
                for key, value in S.items()}

    result = {}
    basis = S.basis()
    for key, b in basis.items():
        result = merge(result, {add_degrees(key, deg): 
                                     [op(p) for p in b for op in op_list if op(p)!=0] 
                                     for deg, op_list in operators.items()})    
    if result != {} :
        return Subspace(result, operators, add_degrees) #{} <-> operators
    else :
        return None
        
        
##############################################################################
# Character
##############################################################################

def character(S, left_basis=s, right_basis=s, row_symmetry=None):
    """
    Return the bicharacter of the subspace `S` into the given bases. The subspace `S`
    must be a multivariate polynomial subspace projected on isotypic components of `S_n` 
    or a dictionnary of subspaces projected on isotypic components.  
    
    INPUT:
    - ``S`` -- a subspace or a dictionnary of subspaces
    - ``left_basis`` -- a basis of the symmetric functions for the $GL_r$-character
    - ``right_basis`` -- a basis of the symmetric functions for the $S_n$-character
    - ``row_symmetry`` -- use "permutation" to compute using the symmetries on rows
    
    EXAMPLES::
        sage: v = vandermonde(Partition([2,2]))
        sage: gen = {v.multidegree(): [v]}
        sage: op = partial_derivatives(v.parent())
        sage: V = Subspace(gen, op)
        sage: V_iso = IsotypicComponent(V, 4, use_antisymmetry=True)
        sage: op_pol = polarization_operators(2, max_deg = v.degree())
        sage: V_pol = PolarizedSpace(V_iso, op_pol)
        sage: character(V_pol)
        s[] # s[2, 2] + s[1] # s[2, 1, 1] + s[2] # s[1, 1, 1, 1]
        
        sage: op_pol = polarization_operators(2, max_deg = v.degree(), row_symmetry="permutation")
        sage: V_pol = PolarizedSpace(V_iso, op_pol)
        sage: character(V_pol, row_symmetry="permutation")
        s[] # s[2, 2] + s[1] # s[2, 1, 1] + s[2] # s[1, 1, 1, 1]

    """
    if isinstance(S, dict):
        return sum(character(V,
                             left_basis=left_basis, right_basis=right_basis, row_symmetry=row_symmetry) 
                   for V in S.values())
    else:
        basis = S.basis()
        basis_element = list(basis.values()).pop()[0]
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
            for key, value in basis.items():
                if Partition(key[1]) == nu:
                    basis_nu[key[0]] = value

            # Use monomials to compute the character
            if row_symmetry == "permutation":
                for deg, b in basis_nu.items():
                    charac_nu += sum(m(Partition(deg)) for p in b)
                if charac_nu != 0 :
                    if left_basis == s :
                        charac_nu = s(charac_nu).restrict_partition_lengths(r,exact=False)
                    elif left_basis != m :
                        charac_nu = left_basis(charac_nu)

            # Or use directly the degrees
            else:
                for deg, b in basis_nu.items():
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
        
@parallel(4)
def parallel_character(S, operators, row_symmetry="permutation", add_degrees=add_degrees_isotypic):
    """
    Return a dictionnary corresponding to the character of the polarized version of the 
    subspace S.
    """

    V = PolarizedSpace(S, operators, add_degrees=add_degrees)
    charac = character(V, row_symmetry=row_symmetry)
    res = {tuple((tuple(support[0]),tuple(support[1]))): coef for support, coef in charac}
    return res
    
    
def character_quotient(M, N, n, r, left_basis=s, right_basis=s):
    """
    Compute the difference of bicharacter between the subspaces `M` and `N`.
    They have to be subspaces of multivariate polynomials projected on 
    isotypic components of `S_n`. 
    
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
        for key, value in b_tot.items():
            if Partition(key[1]) == nu:
                basis_nu_tot[key[0]] = value
        for key, value in b_ideal.items():
            if Partition(key[1]) == nu:
                basis_nu_ideal[key[0]] = value
                
        # Use the degrees to compute the character
        for deg, b in basis_nu_tot.items():
            charac_nu += sum(prod(q[i]**deg[i] for i in range(0,len(deg))) for p in b)
        for deg, b in basis_nu_ideal.items():
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

def factorize(f, n=0):
    """
    Return the factorization of the tensor product `f` w.r.t the right symmetric
    functions. The right symmetric functions have their supports in the partitions
    on `n`. 
    
    INPUT:
    - ``f`` -- a sum of tensor products on symmetric functions
    - ``n`` -- an Integer
    
    EXAMPLES::
    sage: factorize(E_mu(Partition([3,1])), 4)
    [((3, 1), s[]),
     ((1, 1, 1, 1), s[1, 1] + s[3]),
     ((2, 2), s[1]),
     ((2, 1, 1), s[1] + s[2]),
     ((4,), 0)]

    TODO : Delete n and correct code and worksheets 
    """
    SymmetricFunctions(QQ).s()
    supp = sorted(f.support())
    n = f.support().pop()[1].size()
    result = {}
    res = []
    for mu in Partitions(n):
        result[mu] = []
        for (a, b), c in zip(supp, f.coefficients()):
            if b == mu :
                result[mu] += [(a,c)]
    result2 = [(tuple(mu),sum(c*s(nu) for (nu,c) in result[mu])) for mu in result.keys()]
    return result2
    
def latex_output_character(f):
    """
    Return the latex code of the character `f`. 
    
    INPUT:
    - ``f`` -- a sum of tensor products
    
    EXAMPLES:: 
        sage: for mu in Partitions(3):
        ....:     print(latex_output_character(E_mu(mu)))
        1 \otimes s_{3} +(s_{1} + s_{2}) \otimes s_{2,1} +(s_{1,1} + s_{3}) \otimes s_{1,1,1} 
        1 \otimes s_{2,1} + s_{1} \otimes s_{1,1,1} 
        1 \otimes s_{1,1,1} 

    """
    n = f.support().pop()[1].size()
    tensor = sorted(factorize(f, n), reverse=True)
    output = ''
    for a,b in tensor:
        if b != 0 :
            if b == s([]) or b == 1:
                b = 1
                output += str(b)
            elif len(b) > 1:
                output += "(%s)"%latex(b)
            else:
                output += latex(b)
            output += " \otimes %s +"%latex(s(a))
    output = output[:len(output)-1]
    return output
        
def dimension(f, n):
    """
    Return the dimension of the tensor product `f` w.r.t the right symmetric
    functions. The right symmetric functions have their supports in the partitions
    on `n` and they reprensent characters of `S_n`. 
    
    INPUT:
    - ``f`` -- a sum of tensor products on symmetric functions
    - ``n`` -- an Integer
    
    
    EXAMPLES::
        sage: f = E_mu(Partition([3,1]))
        sage: dimension(f, 4)
        [((3, 1), 1), ((1, 1, 1, 1), 1), ((2, 2), 1), ((2, 1, 1), 2)]
        sage: dimension(E_mu(Partition([3])),3)
        [((1, 1, 1), 1), ((3,), 1), ((2, 1), 2)]

    """
    supp = sorted(f.support())
    result = {}
    res = []
    for mu in Partitions(n):
        result[mu] = []
        for (a, b), c in zip(supp, f.coefficients()):
            if b == mu :
                result[mu] += [(a,c)]
    result2 = [(mu,sum(c*s(nu) for (nu,c) in result[mu]).expand(1, alphabet=['q'])) for mu in result.keys() if result[mu]!=[]]
    q = result2[0][1].parent().gens()[0]
    return [(tuple(a), b.subs({q:1})) for a,b in result2]


##############################################################################
# Main function
############################################################################## 

@persist(hash=lambda k: 'character_%s_%s' % (k[0][1].size(),''.join(str(i) for i in k[0][1])),
        funcname='character')
def E_mu(mu, use_antisymmetry=True, row_symmetry="permutation", parallel=False, r=0):
    """
    Given a diagram `mu`, compute the character associated to this diagram.
    Compute the subspace span by the Vandermonde determinant associated to `mu`
    and closed by partial derivatives and polarization, and return its bicaracter.
    If `use_antisymmetry` is `True`, use the optimisation on antisymmetries, and if
    `row_symmetry` is "permutation", use the optimisation on row permutation. 
    
    INPUT:
    - ``mu`` -- a Partition or a Diagram
    - ``use_antisymmetry`` -- a boolean
    - ``row_symmetry`` -- only implemented case "permutation" 
    
    EXAMPLES::
        sage: E_mu(Partition([2,1,1]))
        s[] # s[2, 1, 1] + s[1] # s[1, 1, 1, 1]
        sage: for mu in Partitions(3):
        ....:     print(E_mu(mu))
        s[] # s[3] + s[1] # s[2, 1] + s[1, 1] # s[1, 1, 1] + s[2] # s[2, 1] + s[3] # s[1, 1, 1]
        s[] # s[2, 1] + s[1] # s[1, 1, 1]
        s[] # s[1, 1, 1]

    """
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
    if r == 0 :
        r = max(n-1, 1)
    deg = v.degree()
    if deg == 0:
        deg = 1
    op_pol = polarization_operators(r, deg, row_symmetry=row_symmetry)
    if parallel:
        charac = 0
        for (((_,_),_), V_pol) in parallel_character([(subspace, op_pol) for subspace in V_iso.values()]):
            for key, coeff in V_pol.items():
                charac += coeff*tensor([s(key[0]), s(key[1])])
        return charac
    else:
        V_pol = PolarizedSpace(V_iso, op_pol)
        # character
        return character(V_pol, row_symmetry=row_symmetry)
