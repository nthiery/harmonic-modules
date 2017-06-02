##############################################################################
# action on tuples

from sage.rings.polynomial.polydict cimport ETuple
from sage.groups.perm_gps.permgroup_element cimport PermutationGroupElement

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

        sage: %timeit p*s
        10000 loops, best of 3: 65.4 µs per loop
        sage: %timeit p2*s
        10000 loops, best of 3: 73.3 µs per loop
        sage: %timeit p3*s
        10000 loops, best of 3: 188 µs per loop

        sage: %timeit s._act_on_(p,0)
        10000 loops, best of 3: 66.4 µs per loop
        sage: %timeit s._act_on_(p2,0)
        10000 loops, best of 3: 73.4 µs per loop
        sage: %timeit s._act_on_(p3,0)
        10000 loops, best of 3: 189 µs per loop

    After Cythonization:

        sage: %timeit act_on_polynomial(p, s)
        10000 loops, best of 3: 24.5 µs per loop
        sage: %timeit act_on_polynomial(p2, s)
        10000 loops, best of 3: 86.2 µs per loop
        sage: %timeit act_on_polynomial(p3, s)
        1000 loops, best of 3: 730 µs per loop
    """
    R = p.parent()

    # This should be a map_support
    return R({ETuple(sigma._act_on_list_on_position(list(<ETuple>t))): c
              for t, c in p.dict().iteritems() })

    #n = R.ngens()
    #return R({tuple(t[sigma(i)-1] for i in range(1,n+1)): c
    #          for t,c in p.dict().iteritems() })
