#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.categories.cartesian_product import cartesian_product
from sage.rings.integer_ring import ZZ

def add_degree(d1,d2):
    """
    Compute the sum componentwise of d1 and d2 and return a grading set
    with no negative component as result.
    
    INPUT:
        - ``d1``,``d2`` -- lists of integers
    
    EXAMPLES::
        
        sage: D = cartesian_product([ZZ for i in range(3)])
        sage: add_degree(D([3,2,1]), D([-2,0,0]))
        (1, 2, 1)
        sage: add_degree(D([3,2,1]), D([-2,1,4]))
        (1, 3, 5)
        sage: add_degree(D([3,2,1]), D([2,1,1]))
        (5, 3, 2)
        sage: add_degree(D([3,2,1]), D([2,1,-2]))
        Traceback (most recent call last):
        ...
        ValueError: invalid degree
    """
    d = d1 + d2
    if not all(i>=0 for i in d):
        raise ValueError("invalid degree")
    return d
