#!/usr/bin/env python
# -*- coding: utf-8 -*-

def add_degree(d1,d2):
    d = d1 + d2
    if not all(i>=0 for i in d):
        raise ValueError("invalid degree")
    return d

def add_degree_symmetric(d1,d2):
    """
    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ,4,3)
        sage: D = P._grading_set
        sage: P._add_degree_symmetric(D([3,2,1]), D([-2,0,0]))
        (2, 1, 1)
        sage: P._add_degree_symmetric(D([3,2,1]), D([-2,1,4]))
        (5, 3, 1)
        sage: P._add_degree_symmetric(D([3,2,1]), D([2,1,1]))
        (5, 3, 2)
        sage: P._add_degree_symmetric(D([3,2,1]), D([2,1,-2]))
        Traceback (most recent call last):
        ...
        ValueError: invalid degree
    """
    d = d1 + d2
    if not all(i>=0 for i in d):
        raise ValueError("invalid degree")
    return self._polRing._grading_set(sorted(d, reverse=True))

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
            sage: DP.add_degree_isotyp(d1,d2)
            (2, [3])

    """
    
    return d1[0]+d2[0], d2[1]

def add_degree_polarization(d1,d2):
    return d1[0]+d2, d1[1]
