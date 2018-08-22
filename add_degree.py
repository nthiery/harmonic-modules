#!/usr/bin/env python
# -*- coding: utf-8 -*-

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

def add_degree_symmetric(d1,d2):
    """
    Compute the sum componentwise of d1 and d2 and return a sorted grading
    set with no negative component as result.
    
    INPUT:
        - ``d1``,``d2`` -- lists of integers
    
    EXAMPLES::
        
        sage: D = cartesian_product([ZZ for i in range(3)])
        sage: add_degree_symmetric(D([3,2,1]), D([-2,0,0]))
        (2, 1, 1)
        sage: add_degree_symmetric(D([3,2,1]), D([-2,1,4]))
        (5, 3, 1)
        sage: add_degree_symmetric(D([3,2,1]), D([2,1,1]))
        (5, 3, 2)
        sage: add_degree_symmetric(D([3,2,1]), D([2,1,-2]))
        Traceback (most recent call last):
        ...
        ValueError: invalid degree
    """
    d = d1 + d2
    D = cartesian_product([ZZ for i in range(len(d))])
    if not all(i>=0 for i in d):
        raise ValueError("invalid degree")
    return D(sorted(d, reverse=True))

def add_degree_isotyp(d1,d2):
    """
    INPUT:
        - ``d1``,``d2`` -- lists containing an integer and a partition

    OUTPUT:
        a list containing the sum of the integers of
        `d1` and `d2` and the partition contained in `d2`

    EXAMPLES::
    
        sage: d1 = (3,[2,1])
        sage: d2 = (-1,[3])
        sage: add_degree_isotyp(d1,d2)
        (2, [3])

    """
    
    return d1[0]+d2[0], d2[1]

def add_degree_polarization(d1,d2):
    """
    INPUT:
        - ``d1`` -- list containing an integer and a partition
        - ``d2`` -- a integer

    OUTPUT:
        a list containing the sum of the integer of
        `d1` and `d2` and the partition contained in `d1`

    EXAMPLES::
    
        sage: d1 = (3,[2,1])
        sage: d2 = -1
        sage: add_degree_polarization(d1,d2)
        (2, [2, 1])

    """
    return d1[0]+d2, d1[1]
    
def add_degree_polarization(d1,d2):
    """
    INPUT:
        - ``d1`` -- list containing an integer and a partition
        - ``d2`` -- a integer

    OUTPUT:
        a list containing the sum of the integer of
        `d1` and `d2` and the partition contained in `d1`

    EXAMPLES::
    
        sage: d1 = (3,[2,1])
        sage: d2 = -1
        sage: add_degree_polarization(d1,d2)
        (2, [2, 1])

    """
    return d1[0]+d2, d1[1]
