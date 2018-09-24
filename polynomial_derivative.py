#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.misc.misc_c import prod
from sage.functions.other import factorial

from sage.structure.element import have_same_parent
from matrix_of_vectors import items_of_vector
from diagonal_polynomial_ring import *

##############################################################################
# Polynomials as differential operators
##############################################################################

def polynomial_derivative_on_basis(e, f):
    """
    Return the differentiation of `f` by `e`.

    INPUT:

    - `e`, `f` -- exponent vectors representing two monomials `X^e` and `X^f`
                  (type: :class:`sage.rings.polynomial.polydict.ETuple`)

    OUTPUT:

    - a pair `(g,c)` where `g` is an exponent vector and `c` a
      coefficient, representing the term `c X^g`, or :obj:`None` if
      the result is zero.

    Let `R=K[X]` be a multivariate polynomial ring. Write `X^e` for
    the monomial with exponent vector `e`, and `p(\partial)` the
    differential operator obtained by substituting each variable `x`
    in `p` by `\frac{\partial}{\partial x}`.

    This returns `X^e(\partial)(X^f)`

    EXAMPLES::

        sage: from sage.rings.polynomial.polydict import ETuple
        sage: polynomial_derivative_on_basis(ETuple((4,0)), ETuple((4,0)))
        ((0, 0), 24)
        sage: polynomial_derivative_on_basis(ETuple((0,3)), ETuple((0,3)))
        ((0, 0), 6)
        sage: polynomial_derivative_on_basis(ETuple((0,1)), ETuple((0,3)))
        ((0, 2), 3)
        sage: polynomial_derivative_on_basis(ETuple((2,0)), ETuple((4,0)))
        ((2, 0), 12)
        sage: polynomial_derivative_on_basis(ETuple((2,1)), ETuple((4,3)))
        ((2, 2), 36)
        sage: polynomial_derivative_on_basis(ETuple((1,3)), ETuple((1,2)))
        sage: polynomial_derivative_on_basis(ETuple((2,0)), ETuple((1,2)))
    """
    g = f.esub(e)
    if any(i < 0 for i in g):
        return None
    return (g, prod(factorial(i)/factorial(j) for (i,j) in zip(f,g)))

def polynomial_derivative(p, q): # this just extends a function by bilinearity; we would want it to be built using ModulesWithBasis
    """
    Return the derivative of `q` w.r.t. `p`.

    INPUT:

    - `p`, `q` -- two polynomials in the same multivariate polynomial ring `\K[X]`

    OUTPUT: a polynomial

    The polynomial `p(\partial)(q)`, where `p(\partial)` the
    differential operator obtained by substituting each variable `x`
    in `p` by `\frac{\partial}{\partial x}`.

    EXAMPLES::

        sage: R = QQ['x,y']
        sage: x,y = R.gens()

        sage: polynomial_derivative(x, x)
        1
        sage: polynomial_derivative(x, x^3)
        3*x^2
        sage: polynomial_derivative(x^2, x^3)
        6*x
        sage: polynomial_derivative(x+y, x^3)
        3*x^2
        sage: polynomial_derivative(x+y, x^3*y^3)
        3*x^3*y^2 + 3*x^2*y^3

        sage: p = -x^2*y + 3*y^2
        sage: q = x*(x+2*y+1)^3

        sage: polynomial_derivative(p, q)
        72*x^2 + 144*x*y + 36*x - 48*y - 24
        sage: -diff(q, [x,x,y]) + 3 * diff(q, [y,y])
        72*x^2 + 144*x*y + 36*x - 48*y - 24
    """
    if not have_same_parent(p,q):
        raise ValueError("p and q should have the same parent")
    R = p.parent()
    result = R.zero() # We would want to use R.sum_of_terms_if_not_None
    for (e1, c1) in items_of_vector(p):
        for (e2, c2) in items_of_vector(q):
            m = polynomial_derivative_on_basis(e1,e2)
            if m is None:
                continue
            (e3,c3) = m
            result += R({e3: c1*c2*c3})
    return result

def fiej(i, j, d): # fiejcoeff_on_highest_weight
    """
    INPUT:

    - `i`, `j`, `d` -- nonnegative integers

    OUTPUT: a nonnegative integer

    Let $f = x\partial_y and e = y\partial_x$, and `p` be a highest
    weight polynomial of weight `d`.  Then `c=fiej(i,j,d)` is such
    that `f^i e^j p = c e^{j-i} p`. `c` is given by the formula::

    .. MATH:: \prod_{k = j-i+1}^j (kd - 2 \binom{k}{2})

    EXAMPLES::

        sage: R = QQ['x,y']
        sage: R.inject_variables()
        Defining x, y
        sage: def f(p): return x*diff(p,y)
        sage: def e(p): return y*diff(p,x)

        sage: fiej(0,0,3)
        1

        sage: fiej(0,1,3)
        1
        sage: f(e(x^3)) / x^3
        3
        sage: fiej(1,1,3)
        3
        sage: f(f(e(x^3)))
        0
        sage: fiej(2,1,3)
        0

        sage: fiej(0,2,3)
        1
        sage: f(e(e(x^3))) / e(x^3)
        4
        sage: fiej(1,2,3)
        4
        sage: f(f(e(e(x^3)))) / x^3
        12
        sage: fiej(2,2,3)
        12


        sage: fiej(0,3,3)
        1
        sage: f(e(e(e(x^3)))) / e(e(x^3))
        3
        sage: fiej(1,3,3)
        3
        sage: f(f(e(e(e(x^3))))) / e(x^3)
        12
        sage: f(f(f(e(e(e(x^3)))))) / x^3
        36
        sage: fiej(3,3,3)
        36
        sage: fiej(4,3,3)
        0

        sage: f(f(f(e(e(e(x^9)))))) / x^9
        3024
        sage: fiej(3,3,9)
        3024
    """
    return binomial(j, i) * binomial(d-j+i,i) * factorial(i)**2
    #return prod( k*d - 2*binomial(k,2) for k in range(j-i+1,j+1) )

def string_matrix(d, l):
    """
    Return the string matrix for `d`, `l`

    Let `p = \sum e^j p^{(j)}` where each `p^{(j)}` is a highest
    weight vector, and the sum is homogeneous.

    Then `f^i(p)` is also a linear combination of the e^j

    This return a matrix whose `i`-th row contains the coefficients of
    the expansion of `f^i(p)` as a linear combination of the
    `e^(j-i)p^{(j)}`.
    """
    return matrix(l, l, lambda i,j: fiej(i,j,d+2*j))

"""

Consistency checks::
    sage: P = DiagonalPolynomialRing(QQ,2,1) #not tested
    sage: for mu in Partitions(2): #not tested
    ....:     assert P.harmonic_space_by_shape(mu,use_lie='multipolarization').hilbert_polynomial() == harmonic_character(mu) #not tested

    sage: P = DiagonalPolynomialRing(QQ,3,2) #not tested
    sage: for mu in Partitions(3): #not tested
    ....:     assert P.harmonic_space_by_shape(mu,use_lie='multipolarization').hilbert_polynomial() == harmonic_character(mu) #not tested

This does not work yet::

    sage: P = DiagonalPolynomialRing(QQ,4,3) #not tested
    sage: for mu in Partitions(4): #not tested
    ....:     assert P.harmonic_space_by_shape(mu,use_lie='multipolarization').hilbert_polynomial() == harmonic_character(mu) #not tested
    AssertionError

    sage: mu #not tested
    [2, 1, 1]
    sage: harmonic_character(mu) #not tested
    s[1, 1] + s[2, 1] + s[3] + s[3, 1] + s[4] + s[5]
    sage: P.harmonic_space_by_shape(mu,use_lie='multipolarization').hilbert_polynomial() #not tested
    s[1, 1] + s[2, 1] + s[3] + s[4] + s[5]

Somehow missing 3,1 by polarizing from 5???

"""
