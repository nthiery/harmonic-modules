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
        sage: add_degrees_isotypic(d1, d2)
        ((2, 0), [2, 1])
        sage: add_degrees_isotypic(([2,0,1],[3,2]), [-1,0,0])
        ((1, 0, 1), [3, 2])
        sage: add_degrees_isotypic(([2,0,1],[3,2]), [-1,-1,0])
        Traceback (most recent call last):
        ...
        ValueError: invalid degree
    """
    D = cartesian_product([ZZ for i in range(len(gen_deg[0]))])
    d = D(gen_deg[0])+D(op_deg)
    if not all(i>=0 for i in d):
        raise ValueError("invalid degree")
    return d, gen_deg[1]
    
def add_degrees_symmetric(gen_deg, op_deg):
    """
    Compute the sum componentwise of the lists of integrers contained in d1 and d2 
    and return an ordered grading set and the partition contained in d2 as result.
    
    INPUT:
        - ``d1`` -- list containing a list of integers and a partition
        - ``d2`` -- list of integers

    EXAMPLES::
        sage: d1 = ([0,3],[2,1])
        sage: d2 = [0,-1]
        sage: add_degrees_symmetric(d1, d2)
        ((2, 0), [2, 1])
        sage: add_degrees_symmetric(([2,0,1],[3,2]), [-1,0,0])
        ((1, 1, 0), [3, 2])
    """
    D = cartesian_product([ZZ for i in range(len(gen_deg[0]))])
    d1, d2 = add_degrees_isotypic(gen_deg, op_deg)
    return D(sorted(d1, reverse=True)), d2
