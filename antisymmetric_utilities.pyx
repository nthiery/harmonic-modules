from sage.structure.parent cimport Parent
from sage.structure.element cimport Element
from sage.rings.polynomial.polydict cimport ETuple

from sage.combinat.partition import Partition, Partitions
from sage.groups.perm_gps.permgroup_element import PermutationGroupElement
import sage.combinat.tableau
from sage.combinat.tableau import StandardTableau, StandardTableaux

cimport utilities
#from utilities cimport diagonal_cmp
#from utilities cimport diagonal_swap
#from utilities cimport items_of_vector

cpdef diagonal_antisort(exponents, int n, int r, list positions_list):
    """
    Sort columns decreasingly at the given positions.

    See :func:`antisymmetric_normal` for details.

    INPUT:

    - ``exponents `` -- a list, seen as an `r\times n` array
    - ``r``, ``n`` -- nonnegative integers
    - ``positions_list`` -- a list of lists of all distinct column indices

    EXAMPLES::

        sage: diagonal_antisort([2,1], 2, 1, [[0,1]])
        ((2, 1), 1)
        sage: diagonal_antisort([1,2], 2, 1, [[0,1]])
        ((2, 1), -1)
        sage: diagonal_antisort([2,2], 2, 1, [[0,1]])

        sage: diagonal_antisort([1,2,3,4], 2, 2, [[0,1]])
        ((2, 1, 4, 3), -1)
        sage: diagonal_antisort([1,2,4,3], 2, 2, [[0,1]])
        ((2, 1, 3, 4), -1)
        sage: diagonal_antisort([2,1,4,3], 2, 2, [[0,1]])
        ((2, 1, 4, 3), 1)
        sage: diagonal_antisort([2,1,3,4], 2, 2, [[0,1]])
        ((2, 1, 3, 4), 1)

        sage: diagonal_antisort([1,2,3], 3, 1, [[0,1,2]])
        ((3, 2, 1), -1)
        sage: diagonal_antisort([1,3,2], 3, 1, [[0,1,2]])
        ((3, 2, 1), 1)
        sage: diagonal_antisort([3,2,1], 3, 1, [[0,1,2]])
        ((3, 2, 1), 1)
        sage: diagonal_antisort([1,2,3,4,5,6], 6, 1, [[0,2,4]])
        ((5, 2, 3, 4, 1, 6), -1)

    With unsorted list of positions, the order is relative to the
    order of positions::

        sage: diagonal_antisort([1,2,3], 3, 1, [[2,1,0]])
        ((1, 2, 3), 1)
        sage: diagonal_antisort([3,2,1], 3, 1, [[2,1,0]])
        ((1, 2, 3), -1)

    Two lists of positions::

        sage: diagonal_antisort([1,2,3,4,5,6], 6, 1, [[0,2,4],[1,3,5]])
        ((5, 6, 3, 4, 1, 2), 1)

    """
    cdef int sign = 1
    cdef int i, j
    cdef list positions
    cdef list _exponents = list(exponents)
    for positions in positions_list:
        for i in range(1, len(positions)):
            for j in range(i-1, -1, -1):
                c = utilities.diagonal_cmp(_exponents, n, r, positions[j], positions[j+1])
                if not c:
                    return None
                if c < 0:
                    utilities.diagonal_swap(_exponents, n, r, positions[j], positions[j+1])
                    sign = -sign
                else:
                    continue
    return ETuple(_exponents), sign
    
cpdef is_diagonal_antisorted(exponents, int n, int r, list positions_list):
    """
    Return True if the columns are decreasingly sorted according to positions.

    INPUT:

    - ``exponents `` -- a list, seen as an `r\times n` array
    - ``r``, ``n`` -- nonnegative integers
    - ``positions_list`` -- a list of list of positions

    EXAMPLES::

        sage: is_diagonal_antisorted([2,1], 2, 1, [[0,1]])
        True
        sage: is_diagonal_antisorted([1,2], 2, 1, [[0,1]])
        False
        sage: is_diagonal_antisorted([1,2,3,4,5,6], 6, 1, [[0,2,4],[1,3,5]])
        False


    """
    cdef int i, j
    cdef list positions
    cdef list _exponents = list(exponents)
    for positions in positions_list:
        for i in range(1, len(positions)):
            for j in range(i-1, -1, -1):
                c = utilities.diagonal_cmp(_exponents, n, r, positions[j], positions[j+1])
                if c < 0:
                    return False
                else:
                    continue
    return True

def antisymmetric_normal(p, int n, int r, list positions):
    """
    Return the `I` antisymmetric normal form of `b_I(p)`.

    INPUT:

    - `p` -- a polynomial in `r` sets of `n` variables
    - `r`, `n` -- nonnegative integers
    - `positions` -- a list of lists of all distinct column indices `(I_i)_i`

    Let `W:=\bigtimes_i S(I_i)` be the direct product of the symmetric
    groups of each `I_i`, seen as acting by permutation of the columns
    of variables. Let `b_I` be the antisymmetrizer w.r.t. `W`.
    Let `P_I=b_I(\R[x_i,j])` be the space of polynomials that are
    antisymmetric w.r.t. `W`.

    A polynomial `b_I(p)` in `P_I` can be uniquely
    written in the form `b_I(q)`, where the monomials of `q`
    have exponent vectors whose columns are decreasingly sorted
    at positions `i,i+1` for `i \in I`.

    We call `q` the `I` *antisymmetric normal form* of `b_I(p)`.

    .. TODO::

        This should be moved to a more general piece of documentation about handling antisymmetries.

    EXAMPLES::

        sage: load("code.py")
        sage: R = DiagonalPolynomialRing(QQ, 4, 2)
        sage: X = R.algebra_generators()
        sage: p = 2 * X[0,0]*X[0,3]^2*X[1,1]*X[1,0]^3 + X[1,3] + 3
        sage: antisymmetric_normal(p, 4, 2, [[0,1,2,3]])
        -2*x00^2*x01*x11^3*x12

    TODO: check the result

        sage: antisymmetric_normal(p, 4, 2, [[0,1]])
        2*x00*x03^2*x10^3*x11
        sage: antisymmetric_normal(p, 4, 2, [[0,3]])
        -2*x00^2*x03*x11*x13^3 - x10

    An example with a collision in the result (failed at some point)::

        sage: R = DiagonalPolynomialRing(QQ, 3, 3)
        sage: R._P.inject_variables()
        Defining x00, x01, x02, x10, x11, x12, x20, x21, x22
        sage: p1 = -2*x10*x11*x20 - 2*x10^2*x21 + 2*x10*x11*x21
        sage: antisymmetric_normal(p1, 3, 3, [[0,1,2]])
        -4*x10*x11*x20 - 2*x10^2*x21


    """
    cdef Parent R = p.parent()
    cdef dict d = {}
    cdef ETuple exponent
    cdef Element c
    for exponent, c in utilities.items_of_vector(p):
        res = diagonal_antisort(exponent, n, r, positions)
        if res:
            exponent, sign = res
            d.setdefault(exponent, 0)
            d[exponent] += sign*c
    return R(d)

def reduce_antisymmetric_normal(p, int n, int r, list positions):
    
    """
    Return the terms of `p` which are antisymmetric normal. 

    INPUT:

    - ``p`` -- a polynomial
    - ``r``, ``n`` -- nonnegative integers
    - ``positions_list`` -- a list of list of positions

    EXAMPLES::

        sage: load("code.py")
        sage: R = DiagonalPolynomialRing(QQ, 4, 2)
        sage: X = R.algebra_generators()
        sage: p = -2*x00^2*x01*x11^3*x12
        sage: reduce_antisymmetric_normal(p,4,1,[[0,1,2,3]])
        -2*x00^2*x01*x11^3*x12
        sage: p = -2*x00^2*x01*x11^3*x12-2*x00^2*x01*x11^3*x12
        sage: reduce_antisymmetric_normal(p,4,1,[[0,1,2,3]])
        -4*x00^2*x01*x11^3*x12

    """
    X = p.parent().gens()
    res = 0
    for exposent, c in utilities.items_of_vector(p) :
        if is_diagonal_antisorted(exposent,n,r,positions) :
            product = 1
            for (x,a) in zip(X,exposent) :
                product = product*(x**a)
            res += c*product
    return res

def antisymmetries_of_tableau(Q):
    if not isinstance(Q,StandardTableau) :
        Q = Partition(Q).initial_tableau()
    return [[i-1 for i in column] for column in Q.conjugate()]
    
    
def row_permutation(n, sigma):
    """
    Return the permutation of the variables induced by a permutation of the rows

    INPUT:

    - ``sigma`` -- a permutation of the rows, as a permutation of `\{1,\ldots,r\}`

    OUTPUT:

    a permutation of the variables, as a permutation of `\{1,\ldots,nr\}`

    EXAMPLES::

        sage: s = PermutationGroupElement([(1,2,4),(3,5)])
        sage: row_permutation(3,s)
        (1,4,10)(2,5,11)(3,6,12)(7,13)(8,14)(9,15)
    """
    return PermutationGroupElement([tuple((i-1)*n + 1 + j for i in c)
                                    for c in sigma.cycle_tuples()
                                    for j in range(n) ])
