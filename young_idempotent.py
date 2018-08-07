#!/usr/bin/env python
# -*- coding: utf-8 -*-

from sage.combinat.partition import Partition, Partitions
from sage.combinat.permutation import Permutation

from sage.calculus.functional import derivative


##############################################################################
# Young idempotent and related functions
##############################################################################


def apply_young_idempotent(p, t, use_antisymmetry=False):
    """
    Apply the Young idempotent indexed by `t` on the polynomial `p`

    INPUT::

    - `t` -- a standard tableau or a partition
    - `p` -- a polynomial on as many variables as there are cells in `t`

    The Young idempotent first symmetrizes `p` according to the
    row stabilizer of `t` and then antisymmetrizes the result according
    to the column stabilizer of `t` (a cell containing `i` in `t`
    being associated to the `i`-th variable (starting at `i=1`)
    of the polynomial ring containing `p`.

    .. TODO:: normalize result

    EXAMPLES::

        sage: x,y,z = QQ['x,y,z'].gens()
        sage: p = x^2 * y
        sage: t = StandardTableau([[1],[2],[3]])
        sage: apply_young_idempotent(p, t)
        x^2*y - x*y^2 - x^2*z + y^2*z + x*z^2 - y*z^2

        sage: apply_young_idempotent(p, Partition([1,1,1]))
        x^2*y - x*y^2 - x^2*z + y^2*z + x*z^2 - y*z^2

        sage: t = StandardTableau([[1,2,3]])
        sage: apply_young_idempotent(p, t)
        x^2*y + x*y^2 + x^2*z + y^2*z + x*z^2 + y*z^2

        sage: apply_young_idempotent(p, Partition([3]))
        x^2*y + x*y^2 + x^2*z + y^2*z + x*z^2 + y*z^2

        sage: t = StandardTableau([[1,2],[3]])
        sage: p = x*y*y^2
        sage: apply_young_idempotent(p, t)
        x^3*y + x*y^3 - y^3*z - y*z^3

        sage: p = x*y*z^2
        sage: apply_young_idempotent(p, t)
        -2*x^2*y*z + 2*x*y*z^2
    """
    if isinstance(t, Partition):
        t = t.initial_tableau()
    p = sum(act(Permutation(sigma),p) for sigma in t.row_stabilizer() )
    if use_antisymmetry:
        antisymmetries = antisymmetries_of_tableau(t)
        p = antisymmetric_normal(p, t.size(), 1, antisymmetries)
    else:
        p = sum(sigma.sign()*act(Permutation(sigma),p) for sigma in t.column_stabilizer() )
    return p

def act(sigma,v) :
    """
    Compute the action of the permutation sigma on the element v.

    INPUT:

        - `sigma` -- a permutation
        - `v` -- a polynomial 
        
    EXAMPLES::
    
        sage: P = PolynomialRing(QQ,5,'x')
        sage: X = P.gens()
        sage: X
        (x0, x1, x2, x3, x4)
        sage: v = X[0]*X[1]+X[2]^2-X[4]
        sage: v
        x0*x1 + x2^2 - x4
        sage: sigma = (2,1,3,4,5)
        sage: act(sigma,v)
        x0*x1 + x2^2 - x4
        sage: sigma = (2,1,4,3,5)
        sage: act(sigma,v)
        x0*x1 + x3^2 - x4
        sage: sigma = (3,1,2,4,5)
        sage: act(sigma,v)
        x1^2 + x0*x2 - x4

    """

    X = v.parent().gens()
    r = len(X)/len(sigma)
    n = len(sigma)
    sub = {}
    for j in range(0,r) :
        sub.update({X[i+n*j]:X[sigma[i]-1+n*j] for i in range (0,n) if i!=sigma[i]-1})
    return v.subs(sub)

def make_deriv_comp_young(x,mu):
    """
    Return a function which corresponds to a partial derivative in `x`
    composed with the young idempotent for the partition `mu`.

    INPUT:
        - `x` -- a variable for the derivation
        - `mu` -- a partition

    EXAMPLES::
        sage: P = DiagonalPolynomialRing(QQ,3,3) # not tested
        sage: X = P.algebra_generators() # not tested
        sage: [make_deriv_comp_young(x,mu) for x in X[0] for mu in Partitions(3)] # not tested

        [<function f at 0x7f7f64111f50>,
         <function f at 0x7f7f64111140>,
         <function f at 0x7f7f64111938>,
         <function f at 0x7f7f64111320>,
         <function f at 0x7f7f64111398>,
         <function f at 0x7f7f641115f0>,
         <function f at 0x7f7f641155f0>,
         <function f at 0x7f7f64115668>,
         <function f at 0x7f7f64115578>]

    """
    def f(p):
        return apply_young_idempotent(derivative(p,x),mu)
    return f
