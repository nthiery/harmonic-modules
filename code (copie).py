# -*- coding: utf-8 -*-
import datetime
import inspect
import functools
import operator
import os
import sage.misc.persist as persist

from sage.misc.cachefunc import cached_method, cached_function
from sage.misc.misc_c import prod
from sage.misc.constant_function import ConstantFunction

from sage.categories.algebras import Algebras
from sage.categories.cartesian_product import cartesian_product
from sage.categories.tensor import tensor

from sage.parallel.decorate import parallel
from sage.structure.element import have_same_parent
from sage.structure.sage_object import load
from sage.structure.parent import Parent

from sage.structure.unique_representation import UniqueRepresentation

from sage.combinat.integer_lists.invlex import IntegerListsLex
from sage.combinat.partition import Partition, Partitions
from sage.combinat.ranker import rank_from_list
from sage.combinat.sf.sf import SymmetricFunctions
import sage.combinat.tableau
from sage.combinat.words.word import Word
from sage.functions.other import binomial

from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from sage.sets.set import Set

from sage.groups.perm_gps.permgroup_element import PermutationGroupElement
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.semirings.non_negative_integer_semiring import NN

from sage.functions.other import factorial

load("code1.pyx")

def annihilator_basis(B, S, action=operator.mul, side='right', ambient=None):
    """
    A generalization of :meth:`Modules.FiniteDimensional.WithBasis.ParentMethods.annihilator_basis`

    Return a basis of the annihilator of a finite set of elements in the span of ``B``

    INPUT:

    - ``B`` -- a finite iterable of vectors (linearly independent???)

    - ``S`` -- a finite iterable of objects

    - ``action`` -- a function (default: :obj:`operator.mul`)

    - ``side`` -- 'left' or 'right' (default: 'right'):
      on which side of ``self`` the elements of `S` acts.

    See :meth:`annihilator` for the assumptions and definition
    of the annihilator.

    EXAMPLES:

    By default, the action is the standard `*` operation. So
    our first example is about an algebra::

        sage: F = FiniteDimensionalAlgebrasWithBasis(QQ).example(); F
        An example of a finite dimensional algebra with basis:
        the path algebra of the Kronecker quiver
        (containing the arrows a:x->y and b:x->y) over Rational Field
        sage: x,y,a,b = F.basis()

    In this algebra, multiplication on the right by `x`
    annihilates all basis elements but `x`::

        sage: x*x, y*x, a*x, b*x
        (x, 0, 0, 0)

    So the annihilator is the subspace spanned by `y`, `a`, and `b`::

        sage: annihilator_basis(F.basis(), [x])
        (y, a, b)

    The same holds for `a` and `b`::

        sage: x*a, y*a, a*a, b*a
        (a, 0, 0, 0)
        sage: annihilator_basis(F.basis(), [a])
        (y, a, b)

    On the other hand, `y` annihilates only `x`::

        sage: annihilator_basis(F.basis(), [y])
        (x,)

    Here is a non trivial annihilator::

        sage: annihilator_basis(F.basis(), [a + 3*b + 2*y])
        (-1/2*a - 3/2*b + x,)

    Let's check it::

        sage: (-1/2*a - 3/2*b + x) * (a + 3*b + 2*y)
        0

    Doing the same calculations on the left exchanges the
    roles of `x` and `y`::

        sage: annihilator_basis(F.basis(), [y], side="left")
        (x, a, b)
        sage: annihilator_basis(F.basis(), [a], side="left")
        (x, a, b)
        sage: annihilator_basis(F.basis(), [b], side="left")
        (x, a, b)
        sage: annihilator_basis(F.basis(), [x], side="left")
        (y,)
        sage: annihilator_basis(F.basis(), [a+3*b+2*x], side="left")
        (-1/2*a - 3/2*b + y,)

    By specifying an inner product, this method can be used to
    compute the orthogonal of a subspace::

        sage: x,y,a,b = F.basis()
        sage: def scalar(u,v): return vector([sum(u[i]*v[i] for i in F.basis().keys())])
        sage: annihilator_basis(F.basis(), [x+y, a+b], scalar)
        (x - y, a - b)

    By specifying the standard Lie bracket as action, one can
    compute the commutator of a subspace of `F`::

        sage: annihilator_basis(F.basis(), [a+b], action=F.bracket)
        (x + y, a, b)

    In particular one can compute a basis of the center of the
    algebra. In our example, it is reduced to the identity::

        sage: annihilator_basis(F.basis(), F.algebra_generators(), action=F.bracket)
        (x + y,)

    But see also
    :meth:`FiniteDimensionalAlgebrasWithBasis.ParentMethods.center_basis`.
    """
    if side == 'right':
        action_left = action
        action = lambda b,s: action_left(s, b)
    B = list(B)
    S = list(S)
    if ambient is None:
        ambient = action(S[0], B[0]).parent()
    mat = matrix(ambient.base_ring(), len(B), 0)

    for s in S:
        mat = mat.augment(
            MatrixOfVectors([action(s, b) for b in B], ambient=ambient)._matrix)

    return tuple(sum(c * B[i] for i,c in v.iteritems())
                 for v in mat.left_kernel().basis())


def e_polarization_degrees(D1, D2):
    """
    Return the degree of an e-multipolarization operator from degree D1 to degree D2

    EXAMPLES::

        sage: e_polarization_degrees([5,0,0],[3,1,0])
        (1, [2, 0])
        sage: e_polarization_degrees([5,0,0],[3,1,0])
        (1, [2, 0])
        sage: e_polarization_degrees([5,0,0],[3,2,0])
        sage: e_polarization_degrees([5,1,0],[3,2,0])
        (1, [2, 0])
        sage: e_polarization_degrees([5,4,0,1],[1,1,0,2])
        (3, [4, 3, 0, 0])
        sage: e_polarization_degrees([5,4,0,1,0,0],[1,1,0,2,0,0])
        (3, [4, 3, 0, 0, 0, 0])
        sage: e_polarization_degrees([5,4,0,1,0,0],[1,1,0,2,0,1])
        sage: e_polarization_degrees([5,4,0,1,0,1],[1,1,0,2,0,0])


    """
    D = [D1i-D2i for D1i,D2i in zip(D1, D2)]
    for i in reversed(range(len(D))):
        if D[i] == -1:
            break
        if D[i] != 0:
            return None
    if i <= 0:
        return None
    D[i] = 0
    if any(D[j] < 0 for j in range(i)):
        return None
    return i, D

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
    Return sigma(v).

    INPUT:

    - `sigma` -- a permutation
    - `v` -- a polynomial 

    """
    
    X = v.parent().gens()
    r = len(X)/len(sigma)
    n = len(sigma)
    sub = {}
    for j in range(0,r) :
        sub.update({X[i+n*j]:X[sigma[i]-1+n*j] for i in range (0,n) if i!=sigma[i]-1})
    return v.subs(sub)



@cached_function
def higher_specht(R, P, Q=None, harmonic=False, use_antisymmetry=False):
    """
    Return a basis element of the coinvariants

    INPUT:

    - `R` -- a polynomial ring
    - `P` -- a standard tableau of some shape `\lambda`, or a partition `\lambda`
    - `Q` -- a standard tableau of shape `\lambda`
             (default: the initial tableau of shape `\lambda`)

    - ``harmonic`` -- a boolean (default False)

    The family `(H_{P,Q})_{P,Q}` is a basis of the space of `R_{S_n}`
    coinvariants in `R` which is compatible with the action of the
    symmetric group: namely, for each `P`, the family `(H_{P,Q})_Q`
    forms the basis of an `S_n`-irreducible module `V_{P}` of type
    `\lambda`.

    If `P` is a partition `\lambda` or equivalently the initial
    tableau of shape `\lambda`, then `H_{P,Q}` is the usual Specht
    polynomial, and `V_P` the Specht module.

    EXAMPLES::

        sage: Tableaux.options.convention="french"

        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         for Q in StandardTableaux(la):
        ....:             print ascii_art(la, P, Q, factor(higher_specht(R, P, Q)), sep="    ")
        ....:             print
        ***      1  2  3      1  2  3    2 * 3
        <BLANKLINE>
        *       2         2
        **      1  3      1  3    (-1) * z * (x - y)
        <BLANKLINE>
        *       2         3
        **      1  3      1  2    (-1) * y * (x - z)
        <BLANKLINE>
        *       3         2
        **      1  2      1  3    (-2) * (x - y)
        <BLANKLINE>
        *       3         3
        **      1  2      1  2    (-2) * (x - z)
        <BLANKLINE>
        *      3      3
        *      2      2
        *      1      1    (y - z) * (-x + y) * (x - z)

        sage: factor(higher_specht(R, Partition([2,1])))
        (-2) * (x - z)

        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         print ascii_art(la, P, factor(higher_specht(R, P)), sep="    ")
        ....:         print
        ***      1  2  3    2 * 3
        <BLANKLINE>
        *       2
        **      1  3    (-1) * y * (x - z)
        <BLANKLINE>
        *       3
        **      1  2    (-2) * (x - z)
        <BLANKLINE>
        *      3
        *      2
        *      1    (y - z) * (-x + y) * (x - z)

        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         for Q in StandardTableaux(la):
        ....:             print ascii_art(la, P, Q, factor(higher_specht(R, P, Q, harmonic=True)), sep="    ")
        ....:             print
        ***      1  2  3      1  2  3    2 * 3
        <BLANKLINE>
        *       2         2
        **      1  3      1  3    (-1/3) * (-x - y + 2*z) * (x - y)
        <BLANKLINE>
        *       2         3
        **      1  3      1  2    (-1/3) * (-x + 2*y - z) * (x - z)
        <BLANKLINE>
        *       3         2
        **      1  2      1  3    (-2) * (x - y)
        <BLANKLINE>
        *       3         3
        **      1  2      1  2    (-2) * (x - z)
        <BLANKLINE>
        *      3      3
        *      2      2
        *      1      1    (y - z) * (-x + y) * (x - z)
        <BLANKLINE>

        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: for la in Partitions(3):
        ....:     for P in StandardTableaux(la):
        ....:         for Q in StandardTableaux(la):
        ....:             print ascii_art(la, P, Q, factor(higher_specht(R, P, Q, harmonic="dual")), sep="    ")
        ....:             print
        ***      1  2  3      1  2  3    2^2 * 3
        <BLANKLINE>
        *       2         2
        **      1  3      1  3    (-2) * (-x^2 - 2*x*y + 2*y^2 + 4*x*z - 2*y*z - z^2)
        <BLANKLINE>
        *       2         3
        **      1  3      1  2    (-2) * (x^2 - 4*x*y + y^2 + 2*x*z + 2*y*z - 2*z^2)
        <BLANKLINE>
        *       3         2
        **      1  2      1  3    (-2) * (-x + 2*y - z)
        <BLANKLINE>
        *       3         3
        **      1  2      1  2    (-2) * (x + y - 2*z)
        <BLANKLINE>
        *      3      3
        *      2      2
        *      1      1    (6) * (y - z) * (-x + y) * (x - z)
        <BLANKLINE>

    This caught two bugs::

        sage: R = DiagonalPolynomialRing(QQ, 6, 1)
        sage: for mu in Partitions(6):             # long time
        ....:     for t in StandardTableaux(mu):
        ....:         p = R.higher_specht(t, harmonic=True, use_antisymmetry=True)
    """
    if not isinstance(P, StandardTableau):
        P = Partition(P).initial_tableau()
    n = P.size()
    assert n == R.ngens()
    if Q is None:
        Q = P.shape().initial_tableau()
    if harmonic == "dual":
        # Computes an harmonic polynomial obtained by applying h as
        # differential operator on the van der mond
        P = P.conjugate()
        Q = Q.conjugate() # Is this really what we want?
        h = higher_specht(R, P, Q)
        vdm = higher_specht(R, Partition([1]*n).initial_tableau())
        return polynomial_derivative(h, vdm)
    elif harmonic:
        # TODO: normalization
        n = R.ngens()
        Sym = SymmetricFunctions(R.base_ring())
        m = Sym.m()
        p = Sym.p()
        d = P.cocharge()
        B = [higher_specht(R, P, Q, use_antisymmetry=use_antisymmetry)] + \
            [higher_specht(R, P2, Q, use_antisymmetry=use_antisymmetry) * m[nu].expand(n, R.gens())
             for P2 in StandardTableaux(P.shape()) if P2.cocharge() < d
             for nu in Partitions(d-P2.cocharge(), max_length=n)]
        if use_antisymmetry:
            antisymmetries = antisymmetries_of_tableau(Q)
            B = [antisymmetric_normal(b, n, 1, antisymmetries) for b in B]
        operators = [p[k].expand(n,R.gens()) for k in range(1,n+1)]
        if use_antisymmetry:
            def action(e, f):
                return antisymmetric_normal(polynomial_derivative(e,f), n, 1, antisymmetries)
        else:
            action = polynomial_derivative
        ann = annihilator_basis(B, operators, action=action, side='left')
        assert len(ann) == 1
        return ann[0]

    exponents = index_filling(P)
    X = R.gens()
    m = R.prod(X[i-1]**d for (d,i) in zip(exponents.entries(), Q.entries()))
    return apply_young_idempotent(m, Q, use_antisymmetry=use_antisymmetry)




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

    sage: P = DiagonalPolynomialRing(QQ,2,1)
    sage: for mu in Partitions(2):
    ....:     assert P.harmonic_space_by_shape(mu,use_lie='multipolarization').hilbert_polynomial() == harmonic_character(mu)

    sage: P = DiagonalPolynomialRing(QQ,3,2)
    sage: for mu in Partitions(3):
    ....:     assert P.harmonic_space_by_shape(mu,use_lie='multipolarization').hilbert_polynomial() == harmonic_character(mu)

This does not work yet::

    sage: P = DiagonalPolynomialRing(QQ,4,3)
    sage: for mu in Partitions(4):
    ....:     assert P.harmonic_space_by_shape(mu,use_lie='multipolarization').hilbert_polynomial() == harmonic_character(mu)
    AssertionError

    sage: mu
    [2, 1, 1]
    sage: harmonic_character(mu)
    s[1, 1] + s[2, 1] + s[3] + s[3, 1] + s[4] + s[5]
    sage: P.harmonic_space_by_shape(mu,use_lie='multipolarization').hilbert_polynomial()
    s[1, 1] + s[2, 1] + s[3] + s[4] + s[5]

Somehow missing 3,1 by polarizing from 5???

"""
