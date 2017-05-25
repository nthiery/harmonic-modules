import functools
import operator

from sage.misc.cachefunc import cached_method
from sage.misc.misc_c import prod

from sage.categories.sets_cat import Sets
from sage.categories.algebras import Algebras

from sage.structure.element_wrapper import ElementWrapper
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from sage.combinat.free_module import CombinatorialFreeModule
from sage.combinat.partition import Partition
from sage.combinat.ranker import rank_from_list
import sage.combinat.tableau

from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from sage.matrix.constructor import matrix
from sage.modules.free_module_element import vector
from sage.rings.rational_field import QQ
from sage.sets.recursively_enumerated_set import RecursivelyEnumeratedSet

from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.semirings.non_negative_integer_semiring import NN


def items_of_vector(v):
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
        sage: list(items_of_vector(p))
        [((1, 0, 0), 2),
         ((1, 1, 0), 2),
         ((0, 0, 0), 1),
         ((2, 0, 0), 1),
         ((0, 1, 0), 2),
         ((0, 2, 0), 1)]

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

class Basis:
    """
    A mutable data structure representing a collection of vectors in row echelon form
    """
    def __init__(self, base_ring):
        self._base_ring = base_ring
        self._rank, self._unrank = sage.combinat.ranker.on_fly()
        self._matrix = matrix(base_ring, 0, 0)

    def plain_vector(self, v):
        """
        Return `v` as a plain vector

        INPUT:

        - ``v`` -- an element of the ambient space

        Invariant: when it's returned, the length of the vector is the
        number of basis elements ranked, which is at least the number
        of columns of the matrix.
        """
        # TODO:
        # - optimize this
        # - implement and use a generic api to recover the items
        assert v.base_ring() == self._base_ring
        rank = self._rank
        d = dict((rank(i), c) for i, c in items_of_vector(v))
        return vector(self._base_ring, len(self._rank.cache), d)

    def extend(self, v):
        m = self._matrix
        r = self.plain_vector(v)
        if len(r) > m.ncols():
            m = m.augment(matrix(self._base_ring, m.nrows(), len(r)-m.ncols()))
        m = m.stack(r)
        m.echelonize()
        if m[-1]:
            self._matrix = m
            return True
        return False

    def cardinality(self):
        return self._matrix.nrows()

class Subspace:
    """
    Construct a subspace from generators and linear operators

    INPUT:

    - ``generators`` -- a list of vectors in some ambient vector space `V`
    - ``operators`` -- a list of linear endomorphism `V` (default: ``[]``)

    Return the smallest subspace of `V` containing ``generators`` and
    stable under the action of the operators.

    EXAMPLES::

        sage: E = CombinatorialFreeModule(QQ, [1,2,4,8,16])
        sage: v = E.an_element(); v
        2*B[1] + 2*B[2] + 3*B[4]
        sage: F = Subspace([v, v], [])
        sage: F.dimension()
        1

        sage: B = E.basis()
        sage: F = Subspace([B[1]-B[2], B[2]-B[4], B[1]-B[4]])
        sage: F.dimension()
        2
        sage: F.matrix()
        [ 1  0 -1]
        [ 0  1 -1]

        sage: E = CombinatorialFreeModule(QQ, [1,2,4,8,16])
        sage: B = E.basis()
        sage: phi = E.module_morphism(lambda i: B[i]+B[2*i] if i <= 8 else E.zero(), codomain=E)
        sage: F = Subspace([phi(B[1])], [phi])
        sage: F.dimension()
        4
        sage: F.matrix()
        [ 1  0  0  0 -1]
        [ 0  1  0  0  1]
        [ 0  0  1  0 -1]
        [ 0  0  0  1  1]

    Computing a subspace of a multivariate polynomial ring::

        sage: P = QQ['x,y,z']
        sage: x,y,z = P.gens()
        sage: F = Subspace([x-y, y-z, x-z])
        sage: F.dimension()
        2
        sage: F.matrix()
        [ 1  0 -1]
        [ 0  1 -1]

    The derivatives of the Van-der-Monde determinant in `n` variables
    spans a space of dimension `n!`::

        sage: Delta = (x-y)*(y-z)*(x-z)
        sage: F = Subspace([Delta], [attrcall("derivative", x) for x in P.gens()])
        sage: F.dimension()
        6

    Computing subalgebras and modules in the algebra of the symmetric
    group::

        sage: S = SymmetricGroup(4)
        sage: A = S.algebra(QQ)
        sage: F = Subspace([A.one()], [functools.partial(operator.mul, A.jucys_murphy(i)) for i in range(1,4)])
        sage: F.dimension()
        4
        sage: F.matrix()
        [1 0 0 0 0 0]
        [0 1 1 0 0 0]
        [0 0 0 1 1 0]
        [0 0 0 0 0 1]

        sage: T = StandardTableaux(4)
        sage: def young_idempotent(t):
        ....:     return A.sum_of_terms((S(sigma), sigma.sign()) for sigma in t.column_stabilizer()) * \
        ....:            A.sum_of_monomials(S(sigma) for sigma in t.row_stabilizer())

        sage: for t in T:
        ....:     print t.shape(), t.shape().dimension(), \
        ....:          Subspace([young_idempotent(t)], \
        ....:                   [functools.partial(operator.mul, s) for s in A.algebra_generators()]).dimension()
        [4] 1 1
        [3, 1] 3 3
        [3, 1] 3 3
        [3, 1] 3 3
        [2, 2] 2 2
        [2, 2] 2 2
        [2, 1, 1] 3 3
        [2, 1, 1] 3 3
        [2, 1, 1] 3 3
        [1, 1, 1, 1] 1 1


    Redoing the derivatives of the Van-der-Monde determinant in `n` variables
    as a graded subspace::

        sage: def add_degrees(d1, d2):
        ....:     d = d1 + d2
        ....:     if d < 0: raise ValueError("Negative degree")
        ....:     return d
        sage: P = QQ['x,y,z']
        sage: x,y,z = P.gens()
        sage: Delta = (x-y)*(y-z)*(x-z)
        sage: F = Subspace(generators={3:[Delta]},
        ....:              operators={-1:[attrcall("derivative", x) for x in P.gens()]},
        ....:              add_degrees=add_degrees)
        sage: F.dimension()
        6
        sage: F.dimensions()
        {0: 1, 1: 2, 2: 2, 3: 1}
        sage: F.hilbert_polynomial()
        q^3 + 2*q^2 + 2*q + 1

        sage: P = QQ['x,y,z,t']
        sage: x,y,z,t = P.gens()
        sage: Delta = apply_young_idempotent(x^3*y^2*z, Partition([1,1,1,1]))
        sage: F = Subspace(generators={6:[Delta]},
        ....:              operators={-1:[attrcall("derivative", x) for x in P.gens()]},
        ....:              add_degrees=add_degrees)
        sage: F.hilbert_polynomial()
        q^6 + 3*q^5 + 5*q^4 + 6*q^3 + 5*q^2 + 3*q + 1
        sage: sage.combinat.q_analogues.q_factorial(4)
        q^6 + 3*q^5 + 5*q^4 + 6*q^3 + 5*q^2 + 3*q + 1
    """

    def __init__(self, generators, operators=[],
                 add_degrees=operator.add,
                 hilbert_parent=None):
        if not isinstance(generators, dict):
            generators = {0: generators}
        self._generators = generators

        ambient = {g.parent() for gens in generators.values() for g in gens}
        assert len(ambient) == 1
        ambient = ambient.pop()
        self._ambient = ambient
        self._base_ring = ambient.base_ring()

        if hilbert_parent is None:
            if generators.keys()[0] in NN:
                hilbert_parent = QQ['q']
        self._hilbert_parent = hilbert_parent

        if not isinstance(operators, dict):
            operators = {0: operators}
        self._operators = operators

        self._bases = {}
        self._todo = []
        self._add_degrees = add_degrees
        for d, gens in generators.iteritems():
            basis = Basis(self._base_ring)
            gens = [v
                    for v in gens
                    if basis.extend(v)]
            self._bases[d] = basis
            self.todo(d, gens)

    def todo(self, d1, vectors):
        todo = self._todo
        for d2, ops in self._operators.iteritems():
            try:
                d3 = self._add_degrees(d1, d2)
            except ValueError:
                continue
            todo.extend((v, d3, op)
                        for v in vectors
                        for op in ops)

    def dimension(self):
        """

        """
        self.finalize()
        return sum(basis.cardinality() for basis in self._bases.values())


    def hilbert_polynomial(self):
        return self._hilbert_parent(self.dimensions())

    def dimensions(self):
        self.finalize()
        return {d: basis.cardinality() for d, basis in self._bases.iteritems()}


    def matrix(self):
        self.finalize()
        assert self._bases.keys() == [0] # only handle the non graded case
        return self._bases[0]._matrix

    @cached_method
    def finalize(self):
        todo = self._todo
        while todo:
            v,d,op = todo.pop()
            w = op(v)
            if d not in self._bases:
                self._bases[d] = Basis(self._base_ring)
            if self._bases[d].extend(w):
                self.todo(d, [w])


def destandardize(self):
    """
    Return the smallest word whose standard permutation is ``self``

    INPUT:

    - ``self`` -- a permutation of 1...n

    OUTPUT: a word in the alphabet 0,...,

    EXAMPLES::

        sage: for p in Permutations(3): print(p, destandardize(p))
        ([1, 2, 3], [0, 0, 0])
        ([1, 3, 2], [0, 1, 0])
        ([2, 1, 3], [1, 0, 1])
        ([2, 3, 1], [1, 1, 0])
        ([3, 1, 2], [1, 0, 0])
        ([3, 2, 1], [2, 1, 0])

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

def index_filling(t):
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

        sage: for t in StandardTableaux([3,2,1]):
        ....:     print ascii_art(t,  index_filling(t), sep="  -->  "); print
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

def apply_young_idempotent(p, t):
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
    p = sum( p*sigma for sigma in t.row_stabilizer() )
    p = sum( p*sigma*sigma.sign() for sigma in t.column_stabilizer() )
    return p

##############################################################################
# Polynomial ring with diagonal action
##############################################################################

class DiagonalPolynomialRing(UniqueRepresentation, Parent):
    """

    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ, 4, 3)
        sage: P.algebra_generators()
        [x00 x01 x02 x03]
        [x10 x11 x12 x13]
        [x20 x21 x22 x23]
    """
    def __init__(self, R, n, r):
        names = ["x%s%s"%(i,j) for i in range(r) for j in range(n)]
        P = PolynomialRing(R, n*r, names)
        self._n = n
        self._r = r
        vars = P.gens()
        self._P = P
        self._vars = matrix([[vars[i*n+j] for j in range(n)] for i in range(r)])
        Parent.__init__(self, facade=(P,), category=Algebras(QQ).Commutative())

    def base_ring(self):
        return self._P.base_ring()

    def algebra_generators(self):
        return self._vars

    def polarization(self, p, i1, i2, d):
        """

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 4, 3)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[1,0]^3*X[1,1]^1 + X[2,1]; p
            x00*x10^3*x11 + x21

            sage: P.polarization(p, 1, 2, 2)
            6*x00*x10*x11*x20
            sage: P.polarization(p, 1, 2, 1)
            3*x00*x10^2*x11*x20 + x00*x10^3*x21

            sage: P.polarization(p, 1, 0, 2)
            6*x00^2*x10*x11

            sage: P.polarization(p, 2, 0, 1)
            x01
        """
        n = self._n
        X = self.algebra_generators()
        return self.sum(X[i2,j]*p.derivative(X[i1,j],d)
                        for j in range(n))

