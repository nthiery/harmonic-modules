#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.misc.cachefunc import cached_method

class OnFly:
    """
    Returns a pair of enumeration functions rank / unrank.

    rank assigns on the fly an integer, starting from 0, to any object
    passed as argument. The object should be hashable. unrank is the
    inverse function; it returns None for indices that have not yet
    been assigned.

    EXAMPLES::

        sage: rank, unrank = on_fly()
        sage: rank('a')
        0
        sage: rank('b')
        1
        sage: rank('c')
        2
        sage: rank('a')
        0
        sage: unrank(2)
        'c'
        sage: unrank(3)
        sage: rank('d')
        3
        sage: unrank(3)
        'd'

    Test pickling::

        sage: import __main__        # Won't be needed when in a proper module / in Sage
        sage: __main__.OnFly = OnFly
        sage: rank1, unrank1 = loads(dumps([rank, unrank]))
        sage: rank1.cache
        {(('a',), ()): 0, (('b',), ()): 1, (('c',), ()): 2, (('d',), ()): 3}
        sage: rank1('a')
        0
        sage: rank1('b')
        1
        sage: rank1('e')
        4
        sage: unrank(4)
        sage: unrank1(4)
        'e'



    .. todo:: add tests as in combinat::rankers
    """
    def count():
        i = 0
        while True:
            yield i
            i+=1

    counter = count()

    def __init__(self):
        self.i = -1

    @cached_method(do_pickle=True)
    def rank(self, x):
        self.i = self.i + 1
        self.unrank.set_cache(x, self.i)
        return self.i

    @cached_method(do_pickle=True)
    def unrank(self, i):
        return None

def on_fly():
    o = OnFly()
    return [o.rank, o.unrank]
