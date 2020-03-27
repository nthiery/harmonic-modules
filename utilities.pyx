from sage.structure.element cimport Element
from sage.rings.polynomial.polydict cimport ETuple
from sage.groups.perm_gps.permgroup_element cimport PermutationGroupElement

import sage.combinat.tableau
from sage.combinat.words.word import Word
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
        sage: sorted(items_of_vector(p))
        [((0, 0, 0), 1),
         ((0, 1, 0), 2),
         ((0, 2, 0), 1),
         ((1, 0, 0), 2),
         ((1, 1, 0), 2),
         ((2, 0, 0), 1)]

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

cpdef list diagonal_swap(list exponents, int n, int r, int j1, int j2):
    """
    Swap in place two columns of a diagonal exponent vector.

    INPUT:

    - ``exponents `` -- a list, seen as an `r\times n` array
    - ``r``, ``n`` -- nonnegative integers
    - ``j1``, ``j2`` -- integers in `0,\ldots,n-1`

    Swap inplace the columnss ``j1`` and ``j2`` in the list ``exponnents``,
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
        exponents[i*n+j1], exponents[i*n+j2] = exponents[i*n+j2], exponents[i*n+j1]

cpdef int diagonal_cmp(list exponents, int n, int r, int j1, int j2):
    """
    Compare lexicographically two columns of a diagonal exponent vector.

    INPUT:

    - ``exponents `` -- a list, seen as an `r\times n` array
    - ``r``, ``n`` -- nonnegative integers
    - ``j1``, ``j2`` -- integers in `0,\ldots,n-1`

    Compare lexicographically the columns ``j1`` and ``j2`` in the
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
    cdef int a
    cdef int b
    for i in range(r):
        a = exponents[i*n+j1]
        b = exponents[i*n+j2]
        if a != b:
            # Using trick from https://docs.python.org/3.0/whatsnew/3.0.html#ordering-comparisons
            return (a > b) - (a < b)
    return 0

cpdef reverse_sorting_permutation(t): # TODO: put "stable sorting" as keyword somewhere
    r"""
    Return a permutation `p` such that  is decreasing

    INPUT:

    - `t` -- a list/tuple/... of numbers

    OUTPUT:

    a minimal permutation `p` such that `w \circ p` is sorted decreasingly

    EXAMPLES::

        sage: t = [3, 3, 1, 2]
        sage: s = reverse_sorting_permutation(t); s
        [1, 2, 4, 3]
        sage: [t[s[i]-1] for i in range(len(t))]
        [3, 3, 2, 1]

        sage: t = [4, 2, 3, 2, 1, 3]
        sage: s = reverse_sorting_permutation(t); s
        [1, 3, 6, 2, 4, 5]
        sage: [t[s[i]-1] for i in range(len(t))]
        [4, 3, 3, 2, 2, 1]
    """
    return ~(Word([-i for i in t]).standard_permutation())


cpdef destandardize(self):
    """
    Return the smallest word whose standard permutation is ``self``

    INPUT:

    - ``self`` -- a permutation of 1...n

    OUTPUT: a word in the alphabet 0,...,

    EXAMPLES::

        sage: for p in Permutations(3): print(p, destandardize(p))
        [1, 2, 3] [0, 0, 0]
        [1, 3, 2] [0, 1, 0]
        [2, 1, 3] [1, 0, 1]
        [2, 3, 1] [1, 1, 0]
        [3, 1, 2] [1, 0, 0]
        [3, 2, 1] [2, 1, 0]

        sage: for p in Permutations(4):
        ....:     assert Word(destandardize(p)).standard_permutation() == p
    """
    n = len(self)
    sigma = ~self
    c = 0
    w = [None] * n
    for i in range(1,n+1):
        w[sigma(i)-1] = c
        if i < n and sigma(i+1) < sigma(i):
            c += 1
    return w

cpdef index_filling(t):
    """
    Return the index filling of this standard tableau.

    INPUT:

    - ``t`` -- a standard tableau

    The index filling of `t` is the semi standard tableau with lowest
    content whose standardized row reading coincides with the row
    reading of `t`.

    Reference: Higher Specht Polynomials for the symmetric group and
    the wreath product, S.  Ariki, T.  Terasoma, H.  Yamada.

    Note: in the above reference, the reading word is instead the
    reverse of the row reading of the transpose of `t`.

    .. TODO::

        Check whether this is the most desirable convention.

    EXAMPLES::

        sage: Tableaux.options.convention="french"

        sage: t = StandardTableau([[1,2,4], [3,5]])
        sage: ascii_art(t, index_filling(t), sep = "  -->  ")
          3  5            1  2
          1  2  4  -->    0  0  1

        sage: for t in StandardTableaux([3,2,1]): #not tested
        ....:     print ascii_art(t,  index_filling(t), sep="  -->  "); print #not tested
          3               2
          2  5            1  3
          1  4  6  -->    0  2  3
        <BLANKLINE>
          4               2
          2  5            1  2
          1  3  6  -->    0  1  2
        <BLANKLINE>
          4               2
          3  5            1  2
          1  2  6  -->    0  0  2
        ...
          6               3
          2  4            1  2
          1  3  5  -->    0  1  2
        ...
          6               2
          4  5            1  1
          1  2  3  -->    0  0  0

    The sum of the entries of the index filling is the cocharge of `t`::

        sage: for t in StandardTableaux(6):
        ....:     assert t.cocharge() == sum(i for row in index_filling(t) for i in row)
    """
    return sage.combinat.tableau.from_shape_and_word(t.shape(), destandardize(t.reading_word_permutation()))

