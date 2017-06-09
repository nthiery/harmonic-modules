##############################################################################
# action on tuples

from sage.structure.parent cimport Parent
from sage.structure.element cimport Element
from sage.rings.polynomial.polydict cimport ETuple
from sage.groups.perm_gps.permgroup_element cimport PermutationGroupElement

from sage.combinat.free_module import CombinatorialFreeModule

cpdef items_of_vector(Element v):
    """
    Return an iterator over the pairs ``(index, coefficient)`` for `v`.

    INPUT::

    - ``v`` -- an element of some some vector space or free module

    EXAMPLES:

    This handles indexed free module elements::

        sage: E = CombinatorialFreeModule(QQ, [1,2,4,8,16])
        sage: v = E.an_element(); v
        2*B[1] + 2*B[2] + 3*B[4]
        sage: list(items_of_vector(v))
        [(1, 2), (2, 2), (4, 3)]

    free module elements::

        sage: v = vector([4,0,1,2])
        sage: list(items_of_vector(v))
        [(0, 4), (2, 1), (3, 2)]

        sage: v = vector([4,0,1,2], sparse=True)
        sage: list(items_of_vector(v))
        [(0, 4), (2, 1), (3, 2)]

    multivariate polynomials::

        sage: P = QQ['x,y,z']
        sage: x,y,z = P.gens()
        sage: p = (x+y+1)^2; p
        x^2 + 2*x*y + y^2 + 2*x + 2*y + 1
        sage: list(items_of_vector(p))
        [((1, 0, 0), 2),
         ((1, 1, 0), 2),
         ((0, 0, 0), 1),
         ((2, 0, 0), 1),
         ((0, 1, 0), 2),
         ((0, 2, 0), 1)]

    univariate polynomials::

        sage: P = ZZ['x']
        sage: x = P.gen()
        sage: (x+2)^3
        x^3 + 6*x^2 + 12*x + 8
        sage: list(items_of_vector(_))
        [(0, 8), (1, 12), (2, 6), (3, 1)]

    elements of quotients::

        sage: C = CyclotomicField(5)
        sage: z = C.gen()
        sage: p = (z+2)^2; p
        zeta5^2 + 4*zeta5 + 4
        sage: list(items_of_vector(p))
        [(0, 4), (1, 4), (2, 1)]
    """
    if isinstance(v, CombinatorialFreeModule.Element):
        return v
    else:
        try:
            return v.dict().items()
        except AttributeError:
            return items_of_vector(v.lift())

cpdef act_on_polynomial(p, PermutationGroupElement sigma):
    """

    EXAMPLES::

        sage: x,y,z,t = QQ['x,y,z,t'].gens()
        sage: s = PermutationGroupElement([(1,2,3,4)])
        sage: p = 2*x^2*y+3*z
        sage: p2 = p^10
        sage: p3 = p^100
        sage: act_on_polynomial(p, s)
        2*x*t^2 + 3*y

    Current implementation in Sage::

        sage: %timeit p*s                             # not tested
        10000 loops, best of 3: 65.4 µs per loop
        sage: %timeit p2*s                            # not tested
        10000 loops, best of 3: 73.3 µs per loop
        sage: %timeit p3*s                            # not tested
        10000 loops, best of 3: 188 µs per loop

        sage: %timeit s._act_on_(p,0)                 # not tested
        10000 loops, best of 3: 66.4 µs per loop
        sage: %timeit s._act_on_(p2,0)                # not tested
        10000 loops, best of 3: 73.4 µs per loop
        sage: %timeit s._act_on_(p3,0)                # not tested
        10000 loops, best of 3: 189 µs per loop

    After Cythonization:

        sage: %timeit act_on_polynomial(p, s)         # not tested
        10000 loops, best of 3: 24.5 µs per loop
        sage: %timeit act_on_polynomial(p2, s)        # not tested
        10000 loops, best of 3: 86.2 µs per loop
        sage: %timeit act_on_polynomial(p3, s)        # not tested
        1000 loops, best of 3: 730 µs per loop
    """
    R = p.parent()

    # This should be a map_support
    return R({ETuple(sigma._act_on_list_on_position(list(<ETuple>t))): c
              for t, c in p.dict().iteritems() })

    #n = R.ngens()
    #return R({tuple(t[sigma(i)-1] for i in range(1,n+1)): c
    #          for t,c in p.dict().iteritems() })

cpdef list diagonal_swap(list exponents, int n, int r, int i1, int i2):
    """
    Swap in place two columns.

    INPUT:

    - ``exponents `` -- a list, seen as an `r\times n` array
    - ``r``, ``n`` -- nonnegative integers
    - ``i1``, ``i2`` -- integers in `0,\ldots,n-1`

    Swap inplace the columnss ``i1`` and ``i2`` in the list ``exponnents``,
    seen as an `r\times n` array.

    EXAMPLES::

        sage: l = [1,2,3,4,5,6,7,8]
        sage: diagonal_swap(l, 4, 2, 1, 3)
        sage: l
        [1, 4, 3, 2, 5, 8, 7, 6]

        sage: l = [1,2,3,4,5,6,7,8]
        sage: diagonal_swap(l, 2, 4, 0, 1)
        sage: l
        [2, 1, 4, 3, 6, 5, 8, 7]
    """
    cdef int i
    for i in range(r):
        exponents[i*n+i1], exponents[i*n+i2] = exponents[i*n+i2], exponents[i*n+i1]

cpdef int diagonal_cmp(list exponents, int n, int r, int i1, int i2):
    """
    Compare lexicographically two columns.

    INPUT:

    - ``exponents `` -- a list, seen as an `r\times n` array
    - ``r``, ``n`` -- nonnegative integers
    - ``i1``, ``i2`` -- integers in `0,\ldots,n-1`

    Compare lexicographically the columns ``i1`` and ``i2`` in the
    list ``exponnents``, seen as an `r\times n` array.

    EXAMPLES::

        sage: l = [1, 1, 2, 2, 0, 1, 1, 0]
        sage: diagonal_cmp(l, 4, 2, 0, 1)
        -1
        sage: diagonal_cmp(l, 4, 2, 1, 0)
        1
        sage: diagonal_cmp(l, 4, 2, 2, 3)
        1
        sage: diagonal_cmp(l, 4, 2, 3, 2)
        -1
        sage: diagonal_cmp(l, 4, 2, 3, 3)
        0
    """
    cdef int i
    cdef int c
    for i in range(r):
        c = cmp(exponents[i*n+i1], exponents[i*n+i2])
        if c:
            return c
    return 0

cpdef diagonal_antisort(exponents, int n, int r, list positions_list):
    """
    Sorts columns decreasingly according to positions.

    INPUT:

    - ``exponents `` -- a list, seen as an `r\times n` array
    - ``r``, ``n`` -- nonnegative integers
    - ``positions_list`` -- a list of list of positions

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
                c = diagonal_cmp(_exponents, n, r, positions[j], positions[j+1])
                if not c:
                    return None
                if c < 0:
                    diagonal_swap(_exponents, n, r, positions[j], positions[j+1])
                    sign = -sign
                else:
                    continue
    return ETuple(_exponents), sign

def antisymmetric_normal(p, int n, int r, list positions):
    """

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
    for exponent, c in items_of_vector(p):
        res = diagonal_antisort(exponent, n, r, positions)
        if res:
            exponent, sign = res
            d.setdefault(exponent, 0)
            d[exponent] += sign*c
    return R(d)
