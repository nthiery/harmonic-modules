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
from sage.combinat.tableau import StandardTableau, StandardTableaux
import sage.combinat.tableau
from sage.combinat.words.word import Word
from sage.functions.other import binomial
from sage.combinat.permutation import Permutation

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

load("old_code/code1.pyx")

class func_persist:
    r"""
    Put ``@func_persist`` right before your function
    definition to cache values it computes to disk.

    -- ``key`` - a function that normalizes the input arguments into a unique key
    -- ``hash`` - a function that takes this key and make it into a string (will be used for the name of the file name storing the result) # TODO: file_name? cache_name?
                  TODO: Document that it shall be injective

    """
    def __init__(self, f, dir='func_persist', prefix=None, hash=hash, key=None):
        from sage.misc.misc import sage_makedirs
        self._func = f
        self._dir  = dir
        if prefix is None:
            prefix = f.__name__
        self._prefix = dir+"/"+prefix
        self._hash = hash
        if key is not None:
            self.key = key
        sage_makedirs(dir)
        self.__doc__ = '%s%s%s'%(\
            f.__name__,
            inspect.formatargspec(*inspect.getargs(f.__code__)),
            f.__doc__)

    def key(self, *args, **kwds):
        return (tuple(args), tuple(kwds.items()))

    def __call__(self, *args, **kwds):
        key = self.key(*args, **kwds)
        h = self._hash(key)
        name = '%s_%s.sobj'%(self._prefix, h)

        if os.path.exists(name):
            key2, val = persist.load(name)
            if key == key2:
                # We save and test equality of keys to avoid
                # the (extremely remote) possibility of a hash
                # collision.  Correctness is crucial in mathematics.
                return val

        val = self._func(*args, **kwds)
        persist.save((key, val), name)
        return val

    def dict(self):
        """
        Return the already computed values
        """
        import glob
        return dict(persist.load(name)
                    for name in glob.glob("%s*.sobj"%self._prefix))

class MatrixOfVectors:
    """
    A mutable data structure representing a collection of vectors as a matrix

    EXAMPLES::

        sage: R = PolynomialRing(QQ, 'x,y,z')
        sage: x,y,z = R.gens()
        sage: M = MatrixOfVectors([x, 2*z, x*y+z, 2*x+z+x*y]); M
        A 4x3 matrix of vectors in Multivariate Polynomial Ring in x, y, z over Rational Field
        sage: M._matrix
        [1 0 0]
        [0 2 0]
        [0 1 1]
        [2 1 1]


    .. NOTE::

        - Currently, adding a new vector is linear in the size of the matrix.
          This could probably be fixed by changing the matrix in place.
        - Currently, the matrix is dense
    """
    def __init__(self, vectors=None, ambient=None, stats={}):
        if vectors is None and not isinstance(ambient, Parent):
            vectors = ambient
            ambient = None
        if ambient is None:
            if vectors is not None:
                ambient = vectors[0].parent()
        self._ambient = ambient
        self._base_ring = ambient.base_ring()
        self._rank, self._unrank = sage.combinat.ranker.on_fly()
        self._matrix = matrix(self._base_ring, 0, 0)
        self._basis = []
        self._words = []
        self._is_echelon = True
        stats.setdefault("add_vector", 0)
        stats.setdefault("extend", 0)
        stats.setdefault("zero", 0)
        stats.setdefault("dimension", 0)
        self._stats = stats
        if vectors:
            for v in vectors:
                self.add_vector(v)

    def __repr__(self):
        """

        EXAMPLES::

            sage: E = CombinatorialFreeModule(QQ, [1,2,4,8,16])
            sage: M = EchelonMatrixOfVectors(ambient=E); M
            A 0x0 echelon matrix of vectors in Free module generated by {1, 2, 4, 8, 16} over Rational Field
            sage: M.extend(E.an_element())
            True
            sage: M
            A 1x3 echelon matrix of vectors in Free module generated by {1, 2, 4, 8, 16} over Rational Field
        """
        m = self._matrix
        return "A %sx%s matrix of vectors in %s"%(m.nrows(), m.ncols(), self.ambient())

    def ambient(self):
        return self._ambient

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
        if not self._ambient.is_parent_of(v):
            raise ValueError("Expected vector in %s; got %s"%(self._ambient, v))
        rank = self._rank
        d = dict((rank(i), c) for i, c in items_of_vector(v))
        return vector(self._base_ring, len(self._rank.cache), d, sparse=False)

    def vector(self, v):
        R = self.ambient()
        unrank = self._unrank
        # TODO: this only works for polynomials!
        return sum(v[i]* R.monomial(*unrank(i)) for i in range(len(v)))

    def vectors(self):
        return tuple(self.vector(v) for v in self._matrix)

    def _add_vector_to_matrix(self, m, v): # append?
        r = self.plain_vector(v)
        if len(r) > m.ncols():
            m = m.augment(matrix(self._base_ring, m.nrows(), len(r)-m.ncols()))
        return m.stack(r)

    def add_vector(self, v):
        """
        Add `v` at the bottom of ``self``
        """
        self._stats["add_vector"] += 1
        self._is_echelon = False
        self._matrix = self._add_vector_to_matrix(self._matrix, v)

    def cardinality(self): # or __len__, nrows ??? or dimension in EchelonMatrixOfVectors ???
        return self._matrix.nrows()

class EchelonMatrixOfVectors(MatrixOfVectors):
    """
    A mutable data structure representing a collection of vectors in row echelon form
    """

    def __repr__(self):
        """

        EXAMPLES::

            sage: E = CombinatorialFreeModule(QQ, [1,2,4,8,16])
            sage: M = EchelonMatrixOfVectors(ambient=E); M
            A 0x0 echelon matrix of vectors in Free module generated by {1, 2, 4, 8, 16} over Rational Field
            sage: M.extend(E.an_element())
            True
            sage: M
            A 1x3 echelon matrix of vectors in Free module generated by {1, 2, 4, 8, 16} over Rational Field
        """
        m = self._matrix
        return "A %sx%s echelon matrix of vectors in %s"%(m.nrows(), m.ncols(), self.ambient())

    def extend(self, v, word=None):
        self._stats["extend"] += 1
        if not v:
            self._stats["zero"] += 1
            return False
        assert self._is_echelon
        m = self._add_vector_to_matrix(self._matrix, v)
        m.echelonize()
        if m[-1]:
            self._stats['dimension'] += 1
            self._matrix = m
            self._basis.append(v)
            if word is not None:
                self._words.append(word)
            return True
        return False

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


class Subspace(object):
    """
    Construct a subspace from generators and linear operators

    INPUT:

    - ``generators`` -- a list of vectors in some ambient vector space `V`
    - ``operators`` -- a list of linear endomorphism `V` (default: ``[]``)

    - ``hilbert_parent`` -- a function that, given the dimensions of the subspaces
      given as a dictionary { degree: dim } returns the hilbert polynomial

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

    # Invariants:
    #
    # self._todo contains a list of tuples (v, op, d, word) where `v`
    # is a vector on which we need to apply op to produce an element
    # w of degree d and "reduced word" `word`

    def __init__(self, generators, operators={},
                 add_degrees=operator.add,
                 extend_word=ConstantFunction([]),
                 hilbert_parent=None,
                 degree=None,
                 ambient=None,
                 verbose=False):
        self._stats={}
        self._verbose=verbose

        if self._verbose is not False:
            import tqdm
            if isinstance(self._verbose, tqdm.tqdm):
                self._bar = self._verbose
            else:
                self._bar = tqdm.tqdm(leave=True, unit=" extensions")
            if isinstance(self._verbose, str):
                self._bar.set_description(self._verbose)

        self._degree = degree
        if not isinstance(generators, dict):
            if self._degree is None:
                generators = {0: generators}
            else:
                gens = dict()
                for g in generators:
                    d = self._degree(g)
                    gens.setdefault(d, [])
                    gens[d].append(g)
                generators = gens

        self._generators = generators

        if ambient is not None:
            assert all( ambient.is_parent_of(g) for gens in generators.values() for g in gens )
        else:
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
        self._extend_word = extend_word
        for d, gens in generators.iteritems():
            basis = EchelonMatrixOfVectors(ambient=self._ambient, stats=self._stats)
            for g in gens:
                if basis.extend(g):
                    self.todo(g, d, [])
            self._bases[d] = basis

    def todo(self, vector, d1, word):
        todo = self._todo
        for d2, ops in self._operators.iteritems():
            try:
                d3 = self._add_degrees(d1, d2)
            except ValueError:
                continue
            for op in ops:
                new_word = self._extend_word(word, op)
                if new_word is not None:
                    todo.append((vector, op, d3, new_word))

    def dimension(self):
        """

        """
        self.finalize()
        return sum(basis.cardinality() for basis in self._bases.values())

    def basis(self):
        self.finalize()
        basis = {}
        for i,val in self._bases.iteritems() : 
            if val.vectors() != () :
                basis[i] = val.vectors()
        #return sum((basis.vectors() for basis in self._bases.values()), ())
        return basis

    def hilbert_polynomial(self):
        return self._hilbert_parent(self.dimensions())

    def dimensions(self):
        self.finalize()
        return {d: basis.cardinality() for d, basis in self._bases.iteritems()}
        
    def dimensions_isotyp(self):
        self.finalize()
        return {d: basis.cardinality() for d, basis in self._bases.iteritems() 
                        if basis.cardinality() != 0}




    def matrix(self):
        self.finalize()
        assert self._bases.keys() == [0] # only handle the non graded case
        return self._bases[0]._matrix

    def extend(self, v, d=None, word=None):
        if d is None and self._degree is not None:
            d = self._degree(v)
        if d not in self._bases:
            self._bases[d] = EchelonMatrixOfVectors(ambient=self._ambient, stats=self._stats)
        if self._bases[d].extend(v):
            self.todo(v, d, word)
        if self._verbose is not False:
            self._bar.update()
            self._bar.set_postfix({'todo': len(self._todo), 'dimension': self._stats['dimension'],  'zero': self._stats['zero']})

    @cached_method
    def finalize(self):   # compute?
        todo = self._todo
        if not todo:
            return
        while todo:
            v,op,d,word = todo.pop()
            w = op(v)
            if not isinstance(w, (list, tuple)):
                w = [w]
            for w2 in w:
                self.extend(w2, d, word)
        if self._verbose is not False:
            self._bar.set_postfix({'dimension': self._stats['dimension'], 'zero': self._stats['zero']})
            self._bar.close()
            #print "  dimension: %s  extensions: %s"%(self._stats["dimension"], self._stats["extend"])





class HighestWeightSubspace(Subspace):
    def __init__(self, generators,
                 add_degrees=None,
                 degree=None,
                 hilbert_parent=None,
                 antisymmetries=None,
                 ambient=None,
                 verbose=False):
        Subspace.__init__(self, generators,
                 degree=degree,
                 add_degrees=add_degrees,
                 hilbert_parent=hilbert_parent,
                 ambient=ambient,
                 verbose=verbose)
        self._antisymmetries=antisymmetries

    @cached_method
    def finalize(self):
        R = self._ambient
        r = R._r
        assert all( not any(d[1:])
                    for d in self._bases.keys() )
        maxd = max(d[0] for d in self._bases.keys() )
        degrees = [tuple(D) for D in IntegerListsLex(max_sum=maxd, length=r, max_slope=0)]
        for D2 in degrees:
            # Apply multi polarization operators from subspaces of higher degree
            for D1 in self._bases.keys():
                D = e_polarization_degrees(D1, D2)
                if not D:
                    continue
                i, D = D
                if sum(D) == 1:
                    continue
                for p in self._bases[D1].vectors():
                    q = R.multi_polarization(p, D, i, antisymmetries=self._antisymmetries)
                    self.extend(q, D2)
            if D2 not in self._bases: # no vector of this degree was found
                continue
            # Intersect with highest weight space
            basis = self._bases[D2]
            operators = [functools.partial(R.polarization, i1=i1, i2=i2, d=1,
                                           antisymmetries=self._antisymmetries)
                         for i1 in range(1, R._r)
                         for i2 in range(i1)]
            highest_weight_space = annihilator_basis(basis._basis, operators, action=lambda b, op: op(b), ambient=R)
            self._bases[D2] = MatrixOfVectors( # Could possibly be EchelonMatrixOfVectors?
                highest_weight_space,
                ambient=R,
                )
        return "finished"

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

def antisymmetries_of_tableau(Q):
    if not isinstance(Q,StandardTableau) :
        Q = Partition(Q).initial_tableau()
    return [[i-1 for i in column] for column in Q.conjugate()]

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

def reverse_sorting_permutation(t): # TODO: put "stable sorting" as keyword somewhere
    r"""
    Return a permutation `p` such that  is decreasing

    INPUT:

    - `t` -- a list/tuple/... of numbers

    OUTPUT:

    a minimal permutation `p` such that `w \circ p` is sorted decreasingly

    EXAMPLES::

        sage: t = [3, 3, 1, 2]
        sage: s = reverse_sorting_permutation(t); s
        [1, 2, 4, 3]
        sage: [t[s[i]-1] for i in range(len(t))]
        [3, 3, 2, 1]

        sage: t = [4, 2, 3, 2, 1, 3]
        sage: s = reverse_sorting_permutation(t); s
        [1, 3, 6, 2, 4, 5]
        sage: [t[s[i]-1] for i in range(len(t))]
        [4, 3, 3, 2, 2, 1]
    """
    return ~(Word([-i for i in t]).standard_permutation())


##############################################################################
# Polynomial ring with diagonal action
##############################################################################

class DiagonalPolynomialRing(UniqueRepresentation, Parent):
    """

    Also the coordinate space of `r\times n` matrices

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
        self._grading_set = cartesian_product([ZZ for i in range(r)]) # ZZ^r
        self._hilbert_parent = PolynomialRing(ZZ, r, 'q')
        self._vars = matrix([[vars[i*n+j] for j in range(n)] for i in range(r)])
        Parent.__init__(self, facade=(P,), category=Algebras(QQ).Commutative())

    def monomial(self, *args):
        return self._P.monomial(*args)

    def _repr_(self):
        """
            sage: DiagonalPolynomialRing(QQ, 5, 3) # indirect doctest
            Diagonal polynomial ring with 3 rows of 5 variables over Rational Field

        """
        return "Diagonal polynomial ring with %s rows of %s variables over %s"%(self._r, self._n, self.base_ring())

    def base_ring(self):
        return self._P.base_ring()

    def algebra_generators(self):
        return self._vars

    def inject_variables(self):
        self._P.inject_variables()

    def multidegree(self, p):
        """
        Return the multidegree of a multihomogeneous polynomial

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,3,2)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[0,1]^2 * X[1,0]^2*X[1,1]^3
            sage: P.multidegree(p)
            (3, 5)
            sage: P.multidegree(P.zero())
            -1
        """
        if not p:
            return -1
        n = self._n
        r = self._r
        v = p.exponents()[0]
        return self._grading_set([sum(v[n*i+j] for j in range(n))
                                  for i in range(r)])

    def random_monomial(self, D):
        """
        Return a random monomial of multidegree `D`

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,3,3)
            sage: D = (3,1,4)
            sage: P.random_monomial(D)          # random
            x00*x01*x02*x10*x20*x21^2*x22

            sage: for i in range(50):
            ....:     assert P.multidegree(P.random_monomial(D)) == D
        """
        X = self.algebra_generators()
        X_by_rows = [Set(list(row)) for row in X]
        return prod( X_by_rows[i].random_element()
                     for i in range(len(D))
                     for j in range(D[i]) )

    def random_element(self, D, l=10):
        """
        Return a "random" multi homogeneous polynomial of multidegree `D`.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,3,3)
            sage: P.random_element((2,0,1))         # random
            x01^2*x20 - x02^2*x20 - x00*x01*x21 - x02^2*x21 + 7/4*x00^2*x22 + x01^2*x22 + 183/184*x01*x02*x22
        """
        K = self.base_ring()
        return sum(K.random_element() * self.random_monomial(D)
                   for i in range(l))

    def row_permutation(self, sigma):
        """
        Return the permutation of the variables induced by a permutation of the rows

        INPUT:

        - ``sigma`` -- a permutation of the rows, as a permutation of `\{1,\ldots,r\}`

        OUTPUT:

        a permutation of the variables, as a permutation of `\{1,\ldots,nr\}`

        EXAMPLES::

            sage: s = PermutationGroupElement([(1,2,4),(3,5)])
            sage: P = DiagonalPolynomialRing(QQ,3,5)
            sage: P.row_permutation(s)
            (1,4,10)(2,5,11)(3,6,12)(7,13)(8,14)(9,15)
        """
        n = self._n
        return PermutationGroupElement([tuple((i-1)*n + 1 + j for i in c)
                                        for c in sigma.cycle_tuples()
                                        for j in range(n) ])

    def polarization(self, p, i1, i2, d, use_symmetry=False, antisymmetries=None):
        """
        Return the polarization `P_{d,i_1,i_2}. p` of `p`.

        Recall that the polarization operator is defined by

        .. MATH:: P_{d,i_1,i_2} := \sum_j x_{i_2,j} \partial_{i_1,j}^d

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
        result = self.sum(X[i2,j]*p.derivative(X[i1,j],d)
                          for j in range(n))
        if use_symmetry and result:
            d = self.multidegree(result)
            if list(d) != sorted(d, reverse=True):
                s = reverse_sorting_permutation(d)
                ss = self.row_permutation(s)
                result = act_on_polynomial(result, ss)
                #substitution = \
                #    dict(sum((zip(X[s[i]-1], X[i])
                #              for i in range(r) if s[i]-1 != i), []
                #            ))
                #result = result.substitute(substitution)
            Partition(self.multidegree(result))
        if antisymmetries and result:
            result = antisymmetric_normal(result, self._n, self._r, antisymmetries)
        return result

    @cached_method
    def derivative_input(self, D, j):
        r = self._r
        X = self.algebra_generators()
        res = []
        for i in range(r):
            res.extend([X[i,j],D[i]])
        return res

    def multi_polarization(self, p, D, i2, antisymmetries=None):
        """
        Return the multi polarization `P_{D,i_2}. p` of `p`.

        The multi polarization operator is defined by

        .. MATH:: P_{D,i_2} := \sum_j x_{i_2,j} \partial_{*,j}^D

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 4, 3)
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[1,0]^3*X[1,1]^1 + X[2,1]; p
            x00*x10^3*x11 + x21

        Usual polarizations::

            sage: P.multi_polarization(p, [0,2,0],2)
            6*x00*x10*x11*x20
            sage: P.multi_polarization(p, [0,1,0],2)
            3*x00*x10^2*x11*x20 + x00*x10^3*x21

            sage: P.multi_polarization(p, [0,2,0], 0)
            6*x00^2*x10*x11

            sage: P.multi_polarization(p, [0,0,1], 0)
            x01

        Multi polarizations::

            sage: P.multi_polarization(p, [1,2,0], 2)
            6*x10*x11*x20
        """
        n = self._n
        X = self.algebra_generators()
        D = tuple(D)
        result = self.sum(X[i2,j]*p.derivative(*(self.derivative_input(D, j)))
                          for j in range(n))
        if antisymmetries and result:
            result = antisymmetric_normal(result, self._n, self._r, antisymmetries)
        return result

    def polarization_operators_by_degree(self, side=None, use_symmetry=False, antisymmetries=None, min_degree=0, inert=0):
        """
        Return the collection of polarization operators acting on harmonic polynomials

        INPUT:

        - ``side`` -- 'down'
        - ``min_degree`` -- a non negative integer `d` (default: `0`)

          if `d>0`, only return the polarization operators of differential degree `>=d`.

        If ``side`` is `down` (the only implemented choice), only
        the operators from `X_{i1}` to `X_{i2}` for `i1<i2` are returned.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 4, 2)
            sage: ops = P.polarization_operators_by_degree(); ops
            {(-1, 1): [<functools.partial object at ...>],
             (1, -1): [<functools.partial object at ...>],
             (-2, 1): [<functools.partial object at ...>],
             (-3, 1): [<functools.partial object at ...>],
             (1, -3): [<functools.partial object at ...>],
             (1, -2): [<functools.partial object at ...>]}

            sage: P.polarization_operators_by_degree(side="down")
            {(-3, 1): [<functools.partial object at ...>],
             (-1, 1): [<functools.partial object at ...>],
             (-2, 1): [<functools.partial object at ...>]}

            sage: P = DiagonalPolynomialRing(QQ, 3, 3)
            sage: P.polarization_operators_by_degree(side="down")
            {(-1, 1, 0): [<functools.partial object at ...>],
             (-2, 1, 0): [<functools.partial object at ...>],
             (-2, 0, 1): [<functools.partial object at ...>],
             (0, -2, 1): [<functools.partial object at ...>],
             (-1, 0, 1): [<functools.partial object at ...>],
             (0, -1, 1): [<functools.partial object at ...>]}

            sage: P.polarization_operators_by_degree(use_lie=True) # not tested (features disabled)
            {(-2, 1, 0): [<functools.partial object at ...>],
             (-2, 0, 1): [<functools.partial object at ...>],
             (0, 1, -1): [<functools.partial object at ...>],
             (0, -2, 1): [<functools.partial object at ...>],
             (1, -1, 0): [<functools.partial object at ...>]}

            sage: P = DiagonalPolynomialRing(QQ, 4, 3)
            sage: ops = P.polarization_operators_by_degree()
            sage: X = P.algebra_generators()
            sage: p = X[0,0]*X[1,0]^3*X[1,1]^1 + X[2,1]; p
            x00*x10^3*x11 + x21
            sage: ops[(1,-2,0)][0](p)
            6*x00^2*x10*x11
            sage: ops[(0,-1,1)][0](p)
            3*x00*x10^2*x11*x20 + x00*x10^3*x21
        """
        n = self._n
        r = self._r-inert
        grading_set = self._grading_set
        return {grading_set([-d if i==i1 else 1 if i==i2 else 0 for i in range(r)]):
                [functools.partial(self.polarization, i1=i1, i2=i2, d=d, use_symmetry=use_symmetry, antisymmetries=antisymmetries)]
                for d in range(min_degree+1, n)
                for i1 in range(0,r)
                for i2 in range(0, r)
                #if ((i1==i2+1 if d==1 else i1<i2) if use_lie else i1<i2 if side == 'down' else i1!=i2)
                if (i1<i2 if side == 'down' else i1!=i2)
               }

    def e(self, i):
        return functools.partial(self.polarization, i1=i, i2=i+1, d=1)

    def f(self, i):
        return functools.partial(self.polarization, i1=i+1, i2=i, d=1)

    def is_highest_weight_vector(self, p, _assert=False):
        for i2 in range(self._r):
            for i1 in range(i2):
                if self.polarization(p, i2, i1, 1):
                    if _assert:
                        assert False
                    else:
                        return False
        return True

    def test_highest_weight_vector(self, p):
        self.is_highest_weight_vector(p, _assert=True)

    def highest_weight_vectors(self, p, i1=None, i2=None):
        """
        Return the "unique" highest weight vectors `p_j, j\geq 0` such
        that `p = \sum e^j p_j`.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ, 4, 2)
            sage: X = P.algebra_generators()
            sage: P.highest_weight_vectors(X[0,0], 0, 1)
            [x00]
            sage: P.highest_weight_vectors(X[0,0], 1, 0)
            [0, x10]

            sage: P.highest_weight_vectors(X[1,0]^3, 0, 1)
            [0, 0, 0, 1/6*x00^3]
            sage: P.test_highest_weight_vectors(X[1,0]^3, 0, 1)

            sage: P.highest_weight_vectors(p, 0, 1)  # not tested
            [-x01*x10 + x00*x11, x00^2 - x01^2]
            sage: P.test_highest_weight_vectors(p, 0, 1)   # not tested

        A random example::

            sage: P = DiagonalPolynomialRing(QQ, 4, 3)
            sage: P.inject_variables()
            Defining x00, x01, x02, x03, x10, x11, x12, x13, x20, x21, x22, x23
            sage: x00, x01, x02, x03, x10, x11, x12, x13, x20, x21, x22, x23 = P._P.gens()
            sage: p = 1/2*x10^2*x11*x20 + 3*x10*x11*x12*x20 + 1/3*x11^2*x12*x20 + 1/2*x10*x11*x12*x21 + x10*x11^2*x22 + 1/15*x10*x11*x12*x22 - 2*x11^2*x12*x22 - 2*x12^3*x22
            sage: res = P.highest_weight_vectors(p); res
            [1/48*x00^2*x01*x10 + 1/4*x00*x01*x02*x10 - 1/48*x01^2*x02*x10 - 1/360*x01*x02^2*x10 - 1/48*x00^3*x11 - 1/8*x00^2*x02*x11 - 5/72*x00*x01*x02*x11 - 1/360*x00*x02^2*x11 + 1/6*x01*x02^2*x11 - 1/8*x00^2*x01*x12 + 13/144*x00*x01^2*x12 + 1/180*x00*x01*x02*x12 - 1/6*x01^2*x02*x12,
            1/48*x00^3*x01 + 1/8*x00^2*x01*x02 + 11/144*x00*x01^2*x02 + 1/360*x00*x01*x02^2 - 1/12*x01^2*x02^2 - 1/12*x02^4]
            sage: [P.multidegree(q) for q in res]
            [(3, 1, 0), (4, 0, 0)]
            sage: for q in res:
            ....:     P.test_highest_weight_vector(q)

        .. TODO:: Check that p is indeed in the span of res

        Failing for the strategy of clearing HW for i1,i2 in increasing revlex  order:

            sage: p = 11*x01*x12*x20*x21^2 + 1/3*x00*x12*x20^2*x22 - 1/8*x02*x11*x20*x22^2


        Failing for the strategy of taking the reduced word 1,0,1, or any repeat thereof:

            sage: p = 891/2097152*x01^3*x02*x10 + 27/1048576*x00^2*x02^2*x10 - 81/16777216*x01*x02^3*x10 + 891/1048576*x00*x01^2*x02*x11 + 243/16777216*x00*x02^3*x11 - 2673/2097152*x00*x01^3*x12 - 27/1048576*x00^3*x02*x12 - 81/8388608*x00*x01*x02^2*x12
        """
        # Define HW_{i1,i2}(q) as the predicate
        #   q highest weight for i1, i2; namely: e_{i1,i2}.q = 0
        # Define HW_{<i1,i2}(q) as the predicate
        #   HW_{i1',i2'}(q) for i1'<i2' with (i1',i2') <_{revlex} (i1,i2)
        # Define similarly HW_{≤i1,i2}(q)
        if i1 is None and i2 is None:
            ps = [p]
            # HR:
            # - p is in the span of ps upon application of e_i,j operators
            # - for any q in ps, HW_{<i1,i2}(q)
            for zut in range(5):
                for i2 in range(self._r-1):
                    for i1 in range(self._r-2,i2-1,-1):
                        ps = [r
                                  for q in ps
                                  for r in self.highest_weight_vectors(q, i1, i1+1)
                                  if r]
            return ps

        # Precondition: HW_{<i1,i2}(p)
        # Goal: produce pjs such that:
        # - p = \sum_j e^j pjs[j]
        # - HW_{≤ i1, i2}(q) for q in pjs
        e = functools.partial(self.polarization, i1=i1, i2=i2, d=1)
        f = functools.partial(self.polarization, i1=i2, i2=i1, d=1)
        D = self.multidegree(p)
        w = D[i1] - D[i2]

        # Invariant: fis[i]: f^i(p)
        fip = p
        fis = []
        while fip:
            fis.append(fip)
            fip = f(fip)

        # Invariants:
        # pjs[j]: None or p_j
        # pijs[j]: None or e^(j-i) p_j
        pjs = [ None for j in range(len(fis)) ]
        epjs = [ None for j in range(len(fis)) ]
        for i in range(len(fis)-1, -1, -1):
            for j in range(i+1, len(pjs)):
                epjs[j] = e(epjs[j])
            r = fis[i] - sum(fiej(i,j,w+2*j) * epjs[j] for j in range(i+1, len(epjs)))
            if r:
                pjs[i] = r / fiej(i,i,w+2*i)
            else:
                pjs[i] = r
            epjs[i] = pjs[i]
        # for i2p in range(i2+1):
        #     for i1p in range(i2p):
        #         for q in pjs:
        #             assert self.polarization(q, i2p, i1p, d=1) == 0
        return pjs

    def test_highest_weight_vectors(self, p, i1, i2):
        e = functools.partial(self.polarization, i1=i1, i2=i2, d=1)
        f = functools.partial(self.polarization, i1=i2, i2=i1, d=1)
        pjs = list(self.highest_weight_vectors(p, i1, i2))
        for q in pjs:
            assert f(q) == 0
        for j in range(len(pjs)):
            for i in range(j):
                pjs[j] = e(pjs[j])
        assert p == sum(pjs)

    def strip_highest_weight_vector(self, p):
        """
        EXAMPLES::

            sage: R = DiagonalPolynomialRing(QQ, 3, 3)
            sage: R.inject_variables()
            Defining x00, x01, x02, x10, x11, x12, x20, x21, x22
            sage: x00, x01, x02, x10, x11, x12, x20, x21, x22 = R._P.gens()
            sage: R.strip_highest_weight_vector(x00)
            (x00, [], 0)
            sage: R.strip_highest_weight_vector(x20)
            (x00, [[1, 1], [0, 1]], 0)
            sage: R.strip_highest_weight_vector(x20^2)
            (4*x00^2, [[1, 2], [0, 2]], 0)
        """
        W = SymmetricGroup(range(self._r))
        w0 = W.long_element().reduced_word()
        word = []
        q = p
        for i in w0:
            l = 0
            while True:
                q2 = self.polarization(q, i+1, i, 1)
                if q2:
                    q = q2
                    l += 1
                else:
                    break
            if l:
                word.append([i,l])
        q2 = q
        for i,l in reversed(word):
            D = self.multidegree(q2)
            w = D[i] - D[i+1]
            for l2 in range(l):
                q2 = self.polarization(q2, i, i+1, 1)
            q2 /= fiej(l, l, w)
        self.test_highest_weight_vector(q)
        return q, word, p-q2

    def highest_weight_vectors_decomposition(self, p):
        """
        EXAMPLES::

            sage: R = DiagonalPolynomialRing(QQ, 3, 3)
            sage: R.inject_variables()
            Defining x00, x01, x02, x10, x11, x12, x20, x21, x22
            sage: x00, x01, x02, x10, x11, x12, x20, x21, x22 = R._P.gens()
            sage: e0 = R.e(0); e1 = R.e(1)
            sage: p = e1(e0(e0(3*x00^3))) + e0(e1(e0(x01*x02^2)))
            sage: R.highest_weight_vectors_decomposition(p)
            [[36*x00^3 + 6*x01*x02^2, [[0, 1], [1, 1], [0, 1]]]]

            sage: p = 1/2*x10^2*x11*x20 + 3*x10*x11*x12*x20 + 1/3*x11^2*x12*x20 + 1/2*x10*x11*x12*x21 + x10*x11^2*x22 + 1/15*x10*x11*x12*x22 - 2*x11^2*x12*x22 - 2*x12^3*x22
            sage: R.highest_weight_vectors_decomposition(p)
            [[3*x00^3*x01 + 18*x00^2*x01*x02 + 11*x00*x01^2*x02 + 2/5*x00*x01*x02^2 - 12*x01^2*x02^2 - 12*x02^4,
            [[0, 3], [1, 1], [0, 1]]],
            [3/4*x00^2*x01*x10 + 9*x00*x01*x02*x10 - 3/4*x01^2*x02*x10 - 1/10*x01*x02^2*x10 - 3/4*x00^3*x11 - 9/2*x00^2*x02*x11 - 5/2*x00*x01*x02*x11 - 1/10*x00*x02^2*x11 + 6*x01*x02^2*x11 - 9/2*x00^2*x01*x12 + 13/4*x00*x01^2*x12 + 1/5*x00*x01*x02*x12 - 6*x01^2*x02*x12,
            [[0, 3], [1, 1]]]]

        On a non trivial highest weight vector::

            sage: f0 = R.f(0)
            sage: f1 = R.f(1)
            sage: p = 891/2097152*x01^3*x02*x10 + 27/1048576*x00^2*x02^2*x10 - 81/16777216*x01*x02^3*x10 + 891/1048576*x00*x01^2*x02*x11 + 243/16777216*x00*x02^3*x11 - 2673/2097152*x00*x01^3*x12 - 27/1048576*x00^3*x02*x12 - 81/8388608*x00*x01*x02^2*x12
            sage: f0(p)
            0
            sage: f1(p)
            0
            sage: R.multidegree(p)
            (4, 1, 0)
            sage: R.highest_weight_vectors_decomposition(p) == [[p, []]]
            True

        Found while computing harmonic::

            sage: R = DiagonalPolynomialRing(QQ, 4, 3)
            sage: R.inject_variables()
            Defining x00, x01, x02, x10, x11, x12, x20, x21, x22
            sage: p = 1/2*x02*x10*x20 - 1/2*x03*x10*x20 - 5/2*x02*x11*x20 + 5/2*x03*x11*x20 - 3/2*x00*x12*x20 - 1/2*x01*x12*x20 + 2*x02*x12*x20 + 3/2*x00*x13*x20 + 1/2*x01*x13*x20 - 2*x03*x13*x20 - 2*x02*x10*x21 + 2*x03*x10*x21 + 2*x00*x12*x21 - 2*x03*x12*x21 - 2*x00*x13*x21 + 2*x02*x13*x21 - 2*x00*x10*x22 + 1/2*x01*x10*x22 + 3/2*x02*x10*x22 + 5/2*x00*x11*x22 - 5/2*x03*x11*x22 - 1/2*x00*x12*x22 + 1/2*x03*x12*x22 - 1/2*x01*x13*x22 - 3/2*x02*x13*x22 + 2*x03*x13*x22 + 2*x00*x10*x23 - 1/2*x01*x10*x23 - 3/2*x03*x10*x23 - 5/2*x00*x11*x23 + 5/2*x02*x11*x23 + 1/2*x01*x12*x23 - 2*x02*x12*x23 + 3/2*x03*x12*x23 + 1/2*x00*x13*x23 - 1/2*x02*x13*x23

            sage: p = x02*x10*x20 - x00*x12*x20
            sage: R.multidegree(p)
            (1, 1, 1)

            sage: q
            x00*x02*x10 - x00^2*x12
            sage: e0(e1(q))
            x02*x10*x20 + x00*x12*x20 - 2*x00*x10*x22
            sage: e1(e0(q))
            2*x02*x10*x20 - x00*x12*x20 - x00*x10*x22


        """
        result = []
        while p:
            q, word, p = self.strip_highest_weight_vector(p)
            result.append([q, word])
        return result

    def higher_specht(self, P, Q=None, harmonic=False, use_antisymmetry=False):
        r"""
        Return the hyper specht polynomial indexed by `P` and `Q` in the first row of variables

        See :func:`higher_specht` for details.

        EXAMPLES::

            sage: R = DiagonalPolynomialRing(QQ, 3, 2)
            sage: R.algebra_generators()
            [x00 x01 x02]
            [x10 x11 x12]

            sage: for la in Partitions(3):
            ....:     for P in StandardTableaux(la):
            ....:         print ascii_art(la, R.higher_specht(P), sep="    ")
            ....:         print
            ....:
            ***    6
            <BLANKLINE>
            *
            **    -x00*x01 + x01*x02
            <BLANKLINE>
            *
            **    -2*x00 + 2*x02
            <BLANKLINE>
            *
            *
            *    -x00^2*x01 + x00*x01^2 + x00^2*x02 - x01^2*x02 - x00*x02^2 + x01*x02^2

            sage: for la in Partitions(3):
            ....:     for P in StandardTableaux(la):
            ....:         print ascii_art(la, R.higher_specht(P, use_antisymmetry=True), sep="    ")
            ....:         print
            ....:
            ***    6
            <BLANKLINE>
            *
            **    -x00*x01
            <BLANKLINE>
            *
            **    -2*x00
            <BLANKLINE>
            *
            *
            *    -x00^2*x01
        """
        X = self.algebra_generators()
        # the self._n forces a multivariate polynomial ring even if n=1
        R = PolynomialRing(self.base_ring(), self._n, list(X[0]))
        H = higher_specht(R, P, Q, harmonic=harmonic, use_antisymmetry=use_antisymmetry)
        return self(H)

    def _add_degree(self, d1,d2):
        d = d1 + d2
        if not all(i>=0 for i in d):
            raise ValueError("invalid degree")
        return d

    def _add_degree_symmetric(self, d1,d2):
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
        return self._grading_set(sorted(d, reverse=True))

    def harmonic_space_by_shape(self, mu, verbose=False, use_symmetry=False, use_antisymmetry=False, use_lie=False, use_commutativity=False):
        """
        Return the projection under the Young idempotent for the
        partition / tableau `mu` of the space of diagonal harmonic
        polynomials.

        This is represented as a collection of subspaces corresponding
        to the row-multidegree (aka `GL_r` weight spaces).

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,4,2)
            sage: F = P.harmonic_space_by_shape([1,1,1,1])
            sage: F.hilbert_polynomial()
            s[3, 1] + s[4, 1] + s[6]

            sage: P = DiagonalPolynomialRing(QQ,3,2)
            sage: F = P.harmonic_space_by_shape([1,1,1])
            sage: F.hilbert_polynomial()
            s[1, 1] + s[3]

            sage: P = DiagonalPolynomialRing(QQ,3,2)
            sage: F = P.harmonic_space_by_shape([1,1,1])
            sage: F.hilbert_polynomial()
            s[1, 1] + s[3]

            sage: P = DiagonalPolynomialRing(QQ,5,2)
            sage: F = P.harmonic_space_by_shape(Partition([3,2]),use_lie='multipolarization', verbose=True)
        """
        mu = Partition(mu)
        r = self._r
        S = SymmetricFunctions(ZZ)
        s = S.s()
        m = S.m()
        generators = [self.higher_specht(t, harmonic=True, use_antisymmetry=use_antisymmetry)
                      for t in StandardTableaux(mu)]

        if use_antisymmetry:
            # FIXME: duplicated logic for computing the
            # antisymmetrization positions, here and in apply_young_idempotent
            antisymmetries = antisymmetries_of_tableau(mu.initial_tableau())
        else:
            antisymmetries = None
        if use_lie:
            # The hilbert series will be directly expressed in terms of the
            # dimensions of the highest weight spaces, thus as a symmetric
            # function in the Schur basis
            def hilbert_parent(dimensions):
                return s.sum_of_terms([Partition(d), c]
                                       for d,c in dimensions.iteritems() if c)
        elif use_symmetry:
            def hilbert_parent(dimensions):
                return s(m.sum_of_terms([Partition(d), c]
                                         for d,c in dimensions.iteritems())
                        ).restrict_partition_lengths(r, exact=False)
        else:
            def hilbert_parent(dimensions):
                return s(S.from_polynomial(self._hilbert_parent(dimensions))
                        ).restrict_partition_lengths(r,exact=False)

        operators = self.polarization_operators_by_degree(side='down',
                                                          use_symmetry=use_symmetry,
                                                          antisymmetries=antisymmetries,
                                                          min_degree=1 if use_lie else 0)
        if use_lie == "euler+intersection":
            operators[self._grading_set.zero()] = [
                functools.partial(lambda v,i: self.polarization(self.polarization(v, i+1,i, 1,antisymmetries=antisymmetries), i,i+1, 1,antisymmetries=antisymmetries), i=i)
                for i in range(r-1)
                ]
        elif use_lie == 'decompose':
            def post_compose(f):
                return lambda x: [q for (q,word) in self.highest_weight_vectors_decomposition(f(x))]
            operators = {d: [post_compose(op) for op in ops]
                         for d, ops in operators.iteritems()}
        elif use_lie == 'multipolarization':
            F = HighestWeightSubspace(generators,
                     ambient=self,
                     add_degrees=self._add_degree, degree=self.multidegree,
                     hilbert_parent = hilbert_parent,
                     antisymmetries=antisymmetries,
                     verbose=verbose)
            return F

        operators_by_degree = {}
        for degree,ops in operators.iteritems():
            d = sum(degree)
            operators_by_degree.setdefault(d,[])
            operators_by_degree[d].extend(ops)
        ranks = {}
        for d, ops in operators_by_degree.iteritems():
            ranker = rank_from_list(ops)
            for op in ops:
                ranks[op] = (d, ranker(op))
        ranker = ranks.__getitem__
        def extend_word(word, op):
            new_word = word + [ranker(op)]
            if use_commutativity and sorted(new_word) != new_word:
                #print "rejected: %s"% new_word
                return None
            #print new_word
            return new_word
        # print operators
        add_degree = self._add_degree_symmetric if use_symmetry else self._add_degree
        F = Subspace(generators, operators=operators,
                     add_degrees=add_degree, degree=self.multidegree,
                     hilbert_parent = hilbert_parent,
                     extend_word=extend_word, verbose=verbose)
        F._antisymmetries = antisymmetries
        return F

    def harmonic_character(self, mu, verbose=False, use_symmetry=False, use_antisymmetry=False, use_lie=False, use_commutativity=False):
        """
        Return the `GL_r` character of the space of diagonally harmonic polynomials
        contributed by a given `S_n` irreducible representation.

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,5,2)
            sage: P.harmonic_character(Partition([3,2]))
            s[2] + s[2, 1] + s[2, 2] + s[3] + s[3, 1] + s[4] + s[4, 1] + s[5] + s[6]
        """
        mu = Partition(mu)
        F = self.harmonic_space_by_shape(mu, verbose=verbose,
                                         use_symmetry=use_symmetry,
                                         use_antisymmetry=use_antisymmetry,
                                         use_lie=use_lie,
                                         use_commutativity=use_commutativity)
        F.finalize()

        if use_lie != "euler+intersection":
            return F.hilbert_polynomial()
        # Otherwise:
        # The hilbert polynomial is expressed directly in terms of the
        # dimensions of the highest weight spaces; however the subspaces that
        # have been computed at this stage may include non highest weight
        # vectors.
        # We compute the intersection with the highest weight space,
        # i.e. the joint kernel of the f operators of the lie algebra
        # which are the polarization operators of degree 0 with i_2 < i_1
        operators = [functools.partial(self.polarization, i1=i1, i2=i2, d=1,
                                       antisymmetries=F._antisymmetries)
                     for i1 in range(1, self._r)
                     for i2 in range(i1)]
        return F._hilbert_parent({mu: len(annihilator_basis(basis._basis, operators, action=lambda b, op: op(b), ambient=self))
                                  for mu, basis in F._bases.iteritems() if basis._basis})

    def harmonic_bicharacter(self, verbose=False, use_symmetry=False, use_antisymmetry=False, use_lie=False):
        """
        Return the `GL_r-S_n` character of the space of diagonally harmonic polynomials

        EXAMPLES::

            sage: P = DiagonalPolynomialRing(QQ,3,2)
            sage: P.harmonic_bicharacter()
            s[] # s[3] + s[1] # s[2, 1] + s[1, 1] # s[1, 1, 1] + s[2] # s[2, 1] + s[3] # s[1, 1, 1]

        """
        s = SymmetricFunctions(ZZ).s()
        def char(mu):
            if verbose:
                print "%s:"%s(mu)
            r = tensor([self.harmonic_space_by_shape(mu, verbose=verbose,
                                                     use_symmetry=use_symmetry,
                                                     use_antisymmetry=use_antisymmetry,
                                                     use_lie=use_lie,
                                                    ).hilbert_polynomial(),
                        s[mu]])
            return r
        # TODO Understand why this does not work in parallel
        #char = parallel()(char)
        #return sum( res[1] for res in char(Partitions(self._n).list()) )
        return sum(char(mu) for mu in Partitions(self._n))

def harmonic_character_plain(mu, verbose=False, parallel=False):
    import tqdm
    mu = Partition(mu)
    n = mu.size()
    if len(mu) == n:
        r = n-1
    else:
        r = n-2
    r = max(r, 1)
    R = DiagonalPolynomialRing(QQ, n, r)
    if verbose:
        progressbar = tqdm.tqdm(unit=" extensions", leave=True, desc="harmonic character for "+str(mu).ljust(mu.size()*3), position=mu.rank() if parallel else 1)
    else:
        progressbar = False
    result = R.harmonic_character(mu, verbose=progressbar,
                                  use_symmetry=True,
                                  use_lie="euler+intersection",
                                  use_antisymmetry=True)
    return {tuple(degrees): dim
            for degrees, dim in result}

def harmonic_character_plain_key(mu, **args):
    return tuple(Partition(mu))
def harmonic_character_plain_hash(mu):
    return str(list(mu)).replace(" ","")[1:-1]
harmonic_character_plain = func_persist(harmonic_character_plain,
                                        hash=harmonic_character_plain_hash,
                                        key= harmonic_character_plain_key)

"""
Migrating persistent database from previous format::

    sage: SymmetricFunctions(ZZ).inject_shorthands()             # not tested
    sage: myhash=lambda mu: str(list(mu)).replace(" ","")[1:-1]
    sage: cd func_persist                                        # not tested
    sage: for filename in glob.glob("harmonic_character*.sobj"): # not tested
    ....:     obj = load(filename)
    ....:     key = obj[0][0][0]
    ....:     value = obj[1]
    ....:     chi = s(m.sum_of_terms([Partition(nu), c] for nu, c in value.iteritems())).restrict_partition_lengths(max(4, len(key)-1), exact=False)
    ....:     print key, chi
    ....:     value = {tuple(nu):c for nu,c in chi }
    ....:     save((key,value), "plain/harmonic_character_plain_%s"%(myhash(key)))

Inserting François's value for the character for `1^6` in the database::

    sage: S = SymmetricFunctions(ZZ)
    sage: s = S.s()
    sage: res = s[1, 1, 1, 1, 1] + s[3, 1, 1, 1] + s[4, 1, 1, 1] + s[4, 2, 1] + s[4, 3, 1] + s[4, 4] + s[4, 4, 1] + s[5, 1, 1, 1] + s[5, 2, 1] + s[5, 3, 1] + s[6, 1, 1] + s[6,1, 1, 1] + s[6, 2, 1] + s[6, 3] + s[6, 3, 1] + s[6, 4] + s[7, 1, 1] + s[7, 2] +s[7, 2, 1] + s[7, 3] + s[7, 4] + 2*s[8, 1, 1] + s[8, 2] + s[8, 2, 1] + s[8, 3] + s[9, 1, 1] + s[9, 2] + s[9, 3] + s[10, 1] + s[10, 1, 1] + s[10, 2] + s[11, 1] + s[11, 2] + s[12, 1] + s[13, 1] + s[15]
    sage: key=tuple([1,1,1,1,1,1])
    sage: value = {tuple(mu):c for mu,c in res}
    sage: myhash=lambda mu: str(list(mu)).replace(" ","")[1:-1]
    sage: save((key,value), "func_persist/harmonic_character_plain_%s"%(myhash(key))) # not tested
"""

def harmonic_character(mu):
    """
    Return the `GL_n` character of an `S_n` isotypic component in the
    diagonal harmonic polynomials

    Let `H` be the space of diagonal harmonic harmonic polynomials on
    `k\times n` variables, with `k` large enough.  Write its `GL_k
    \times S_n` bicharacter as `\sum f_\mu \otimes s_\mu`.  This
    computes `f_\mu`.

    EXAMPLES::

        sage: harmonic_character([6])
        s[]
        sage: harmonic_character([5, 1])
        s[1] + s[2] + s[3] + s[4] + s[5]
        sage: harmonic_character([4, 2])
        s[2] + s[2, 1] + s[2, 2] + s[3] + s[3, 1] + s[3, 2] + 2*s[4] + 2*s[4, 1] + s[4, 2] + s[5] + s[5, 1] + 2*s[6] + s[6, 1] + s[7] + s[8]
        sage: harmonic_character([4, 1, 1])
        s[1, 1] + s[2, 1] + s[3] + 2*s[3, 1] + s[3, 2] + s[3, 3] + s[4] + 2*s[4, 1] + s[4, 2] + 2*s[5] + 2*s[5, 1] + s[5, 2] + 2*s[6] + s[6, 1] + 2*s[7] + s[7, 1] + s[8] + s[9]
        sage: harmonic_character([3, 3])
        s[2, 2] + s[2, 2, 1] + s[3] + s[3, 1] + s[3, 2] + s[4, 1] + s[4, 1, 1] + s[4, 2] + s[5] + s[5, 1] + s[5, 2] + s[6] + s[6, 1] + s[7] + s[7, 1] + s[9]
        sage: harmonic_character([2, 2, 2])
        s[2, 2] + s[2, 2, 1] + s[3, 1, 1] + s[3, 1, 1, 1] + s[3, 2, 1] + s[3, 3, 1] + s[4, 1] + s[4, 1, 1] + 2*s[4, 2] + s[4, 2, 1] + s[4, 3] + s[4, 4] + s[5, 1] + 2*s[5, 1, 1] + 2*s[5, 2] + s[5, 2, 1] + s[5, 3] + s[6] + 2*s[6, 1] + s[6, 1, 1] + 2*s[6, 2] + s[6, 3] + 2*s[7, 1] + s[7, 1, 1] + s[7, 2] + s[8] + 2*s[8, 1] + s[8, 2] + s[9] + s[9, 1] + s[10] + s[10, 1] + s[12]
        sage: harmonic_character([3, 1, 1, 1])
        s[1, 1, 1] + s[2, 1, 1] + s[3, 1] + 2*s[3, 1, 1] + s[3, 2] + s[3, 2, 1] + 2*s[3, 3] + s[3, 3, 1] + 2*s[4, 1] + 2*s[4, 1, 1] + 2*s[4, 2] + s[4, 2, 1] + 2*s[4, 3] + 3*s[5, 1] + 2*s[5, 1, 1] + 3*s[5, 2] + s[5, 2, 1] + 2*s[5, 3] + s[6] + 4*s[6, 1] + s[6, 1, 1] + 3*s[6, 2] + s[6, 3] + s[7] + 4*s[7, 1] + s[7, 1, 1] + 2*s[7, 2] + 2*s[8] + 3*s[8, 1] + s[8, 2] + 2*s[9] + 2*s[9, 1] + 2*s[10] + s[10, 1] + s[11] + s[12]
        sage: harmonic_character([3, 2, 1])
        s[2, 1] + s[2, 1, 1] + s[2, 2] + s[2, 2, 1] + 2*s[3, 1] + 2*s[3, 1, 1] + 3*s[3, 2] + 2*s[3, 2, 1] + s[3, 3] + s[4] + 3*s[4, 1] + 2*s[4, 1, 1] + 4*s[4, 2] + s[4, 2, 1] + 2*s[4, 3] + 2*s[5] + 5*s[5, 1] + 2*s[5, 1, 1] + 4*s[5, 2] + s[5, 3] + 2*s[6] + 5*s[6, 1] + s[6, 1, 1] + 3*s[6, 2] + 3*s[7] + 4*s[7, 1] + s[7, 2] + 3*s[8] + 3*s[8, 1] + 2*s[9] + s[9, 1] + 2*s[10] + s[11]
        sage: harmonic_character([2, 1, 1, 1, 1])
        s[1, 1, 1, 1] + s[2, 1, 1, 1] + s[3, 1, 1] + s[3, 1, 1, 1] + s[3, 2, 1] + s[3, 3, 1] + 2*s[4, 1, 1] + s[4, 1, 1, 1] + s[4, 2] + 2*s[4, 2, 1] + 2*s[4, 3] + 2*s[4, 3, 1] + s[4, 4] + 3*s[5, 1, 1] + s[5, 1, 1, 1] + s[5, 2] + 2*s[5, 2, 1] + 2*s[5, 3] + s[5, 3, 1] + s[5, 4] + s[6, 1] + 3*s[6, 1, 1] + 3*s[6, 2] + 2*s[6, 2, 1] + 3*s[6, 3] + s[6, 4] + 2*s[7, 1] + 3*s[7, 1, 1] + 3*s[7, 2] + s[7, 2, 1] + 2*s[7, 3] + 3*s[8, 1] + 2*s[8, 1, 1] + 3*s[8, 2] + s[8, 3] + 3*s[9, 1] + s[9, 1, 1] + 2*s[9, 2] + s[10] + 3*s[10, 1] + s[10, 2] + s[11] + 2*s[11, 1] + s[12] + s[12, 1] + s[13] + s[14]
        sage: harmonic_character([2, 2, 1, 1])
        s[2, 1, 1] + s[2, 1, 1, 1] + s[2, 2, 1] + s[3, 1, 1] + s[3, 1, 1, 1] + s[3, 2] + 2*s[3, 2, 1] + s[3, 3] + s[3, 3, 1] + s[4, 1] + 3*s[4, 1, 1] + s[4, 1, 1, 1] + 2*s[4, 2] + 3*s[4, 2, 1] + 2*s[4, 3] + s[4, 3, 1] + s[4, 4] + 2*s[5, 1] + 3*s[5, 1, 1] + 4*s[5, 2] + 2*s[5, 2, 1] + 3*s[5, 3] + s[5, 4] + 3*s[6, 1] + 4*s[6, 1, 1] + 4*s[6, 2] + s[6, 2, 1] + 2*s[6, 3] + s[7] + 4*s[7, 1] + 2*s[7, 1, 1] + 4*s[7, 2] + s[7, 3] + s[8] + 4*s[8, 1] + s[8, 1, 1] + 2*s[8, 2] + 2*s[9] + 4*s[9, 1] + s[9, 2] + s[10] + 2*s[10, 1] + 2*s[11] + s[11, 1] + s[12] + s[13]
        sage: harmonic_character([1, 1, 1, 1, 1, 1])
        s[1, 1, 1, 1, 1] + s[3, 1, 1, 1] + s[4, 1, 1, 1] + s[4, 2, 1] + s[4, 3, 1] + s[4, 4] + s[4, 4, 1] + s[5, 1, 1, 1] + s[5, 2, 1] + s[5, 3, 1] + s[6, 1, 1] + s[6, 1, 1, 1] + s[6, 2, 1] + s[6, 3] + s[6, 3, 1] + s[6, 4] + s[7, 1, 1] + s[7, 2] + s[7, 2, 1] + s[7, 3] + s[7, 4] + 2*s[8, 1, 1] + s[8, 2] + s[8, 2, 1] + s[8, 3] + s[9, 1, 1] + s[9, 2] + s[9, 3] + s[10, 1] + s[10, 1, 1] + s[10, 2] + s[11, 1] + s[11, 2] + s[12, 1] + s[13, 1] + s[15]
    """
    mu = tuple(mu)
    result = harmonic_character_plain(mu)
    S = SymmetricFunctions(ZZ)
    s = S.s()
    return s.sum_of_terms([Partition(d), c] for d,c in result.iteritems())

@parallel()
def harmonic_character_paral(mu):
    r"""
    Utility to parallelize the computation of the `GL_r` character of
    the `S_n` isotypic components in the diagonal harmonic
    polynomials.
    """
    t1 = datetime.datetime.now()
    result = harmonic_character_plain(mu, verbose=True, parallel=True)
    t2 = datetime.datetime.now()
    return result, t2-t1

def harmonic_characters(n):
    r"""
    Compute in parallel the `GL_r` character of all `S_n` isotypic
    components in the diagonal harmonic polynomials.
    """
    S = SymmetricFunctions(ZZ)
    s = S.s()
    for (((nu,),_), (result, t)) in harmonic_character_paral((tuple(mu),) for mu in Partitions(n)):
        import tqdm
        tqdm.tqdm.write("\r%s\t("%Partition(nu)+str(t)[:-7]+"): %s"%
                                                     s.sum_of_terms([Partition(d), c]
                                                                    for d,c in result.iteritems()))

def harmonic_bicharacter(n):
    s = SymmetricFunctions(ZZ).s()
    ss = tensor([s,s])
    return ss.sum(tensor([harmonic_character(mu), s.term(mu)])
                  for mu in Partitions(n))

def harmonic_bicharacter_truncated_series():
    """
    Return the diagonal harmonic bicharacter series, truncated to
    whatever has already been computed and stored in the database.

    OUTPUT: a sum `\sum c_{\lambda,\mu} s_\lambda \tensor s_\mu`

    EXAMPLES::

        sage: Harm = harmonic_bicharacter_truncated_series()

        sage: Sym = SymmetricFunctions(ZZ)
        sage: s = Sym.s(); e = Sym.e(); h = Sym.h()

    Extracting the `S_n` character for a given `GL_r` representation::

        sage: def chi1(mu, p):
        ....:     return s.sum_of_terms([nu,c] for ((mu1,nu),c) in p if mu1 == mu)
        sage: def chi2(nu, p):
        ....:     return e.sum_of_terms([mu,c] for ((mu,nu1),c) in p if nu1 == nu)
        sage: chi1([1,1], Harm)
        s[1, 1, 1] + s[2, 1, 1] + s[3, 1, 1] + s[4, 1, 1]

    Some steps toward recovering it as a product H * finite sum.
    Let's define `H` and its inverse::

        sage: H = sum(h[i] for i in range(0, 10)); H
        h[] + h[1] + h[2] + h[3] + h[4] + h[5] + h[6] + h[7] + h[8] + h[9]
        sage: Hinv = s(1-e[1]+e[2]-e[3]+e[4]-e[5]+e[6])

        sage: truncate(H*Hinv,6)
        h[]

        sage: truncate((1-chi1([1], Harm)    ) * Hinv, 7)
        s[] - s[1]

        sage: truncate((1+chi1([1,1], Harm)  ) * Hinv, 7)
        s[] - s[1] + s[1, 1]

        sage: truncate((1-chi1([1,1,1], Harm)) * Hinv, 7)
        s[] - s[1] + s[1, 1] - s[1, 1, 1]



        sage: bitruncate(Harm * tensor([s.one(), (1-s[1]+s[2]-s[3]+s[4]-s[5])]), 6)
        s[] # s[] - s[] # s[1, 1] + s[] # s[2] + s[] # s[2, 2] - s[] # s[3, 1] + s[] # s[4] + s[1] # s[1, 1] - s[1] # s[1, 1, 1] - s[1] # s[2, 2] + s[1] # s[2, 2, 1] + s[1] # s[3, 1] - s[1] # s[3, 1, 1] + s[1, 1] # s[1, 1, 1] - s[1, 1] # s[1, 1, 1, 1] - s[1, 1] # s[2, 2, 1] + s[1, 1] # s[3, 1, 1] + s[1, 1, 1] # s[1, 1, 1, 1] - s[1, 1, 1] # s[1, 1, 1, 1, 1] + s[1, 1, 1, 1] # s[1, 1, 1, 1, 1] + s[2] # s[2, 1] - s[2] # s[2, 1, 1] + s[2] # s[4, 1] + s[2, 1] # s[2, 1, 1] - s[2, 1] # s[2, 1, 1, 1] + s[2, 1] # s[2, 2] - s[2, 1] # s[2, 2, 1] + s[2, 1, 1] # s[2, 1, 1, 1] + s[2, 1, 1] # s[2, 2, 1] + s[2, 2] # s[2, 2, 1] + s[2, 2] # s[3, 2] + s[3] # s[1, 1, 1] - s[3] # s[1, 1, 1, 1] - s[3] # s[2, 2, 1] + s[3] # s[3, 1] + s[3, 1] # s[1, 1, 1, 1] - s[3, 1] # s[1, 1, 1, 1, 1] + s[3, 1] # s[2, 1, 1] - s[3, 1] # s[2, 1, 1, 1] + s[3, 1] # s[3, 1, 1] + s[3, 1] # s[3, 2] + s[3, 1, 1] # s[1, 1, 1, 1, 1] + s[3, 1, 1] # s[2, 1, 1, 1] + s[3, 1, 1] # s[2, 2, 1] + s[3, 2] # s[2, 1, 1, 1] + s[3, 2] # s[2, 2, 1] + s[3, 2] # s[3, 1, 1] + s[4] # s[2, 1, 1] - s[4] # s[2, 1, 1, 1] + s[4] # s[2, 2] - s[4] # s[2, 2, 1] + s[4] # s[4, 1] + s[4, 1] # s[1, 1, 1, 1] - s[4, 1] # s[1, 1, 1, 1, 1] + s[4, 1] # s[2, 1, 1, 1] + 2*s[4, 1] # s[2, 2, 1] + s[4, 1] # s[3, 1, 1] + s[4, 1] # s[3, 2] + s[5] # s[2, 1, 1] - s[5] # s[2, 1, 1, 1] + s[5] # s[3, 1, 1] + s[5] # s[3, 2]

    Not quite::

        sage: bitruncate(Harm * tensor([s.one(), Hinv]), 6)
        s[] # s[] + s[1] # s[1, 1] - s[1] # s[1, 1, 1] + s[1] # s[1, 1, 1, 1] - s[1] # s[1, 1, 1, 1, 1] + s[1, 1] # s[1, 1, 1] - s[1, 1] # s[1, 1, 1, 1] + s[1, 1] # s[1, 1, 1, 1, 1] + s[1, 1, 1] # s[1, 1, 1, 1] - s[1, 1, 1] # s[1, 1, 1, 1, 1] + s[1, 1, 1, 1] # s[1, 1, 1, 1, 1] + s[2] # s[2, 1] - s[2] # s[2, 1, 1] + s[2] # s[2, 1, 1, 1] + s[2, 1] # s[2, 1, 1] - s[2, 1] # s[2, 1, 1, 1] + s[2, 1] # s[2, 2] - s[2, 1] # s[2, 2, 1] + s[2, 1, 1] # s[2, 1, 1, 1] + s[2, 1, 1] # s[2, 2, 1] + s[2, 2] # s[2, 2, 1] + s[2, 2] # s[3, 2] + s[3] # s[1, 1, 1] - s[3] # s[1, 1, 1, 1] + s[3] # s[1, 1, 1, 1, 1] + s[3] # s[3, 1] - s[3] # s[3, 1, 1] + s[3, 1] # s[1, 1, 1, 1] - s[3, 1] # s[1, 1, 1, 1, 1] + s[3, 1] # s[2, 1, 1] - s[3, 1] # s[2, 1, 1, 1] + s[3, 1] # s[3, 1, 1] + s[3, 1] # s[3, 2] + s[3, 1, 1] # s[1, 1, 1, 1, 1] + s[3, 1, 1] # s[2, 1, 1, 1] + s[3, 1, 1] # s[2, 2, 1] + s[3, 2] # s[2, 1, 1, 1] + s[3, 2] # s[2, 2, 1] + s[3, 2] # s[3, 1, 1] + s[4] # s[2, 1, 1] - s[4] # s[2, 1, 1, 1] + s[4] # s[2, 2] - s[4] # s[2, 2, 1] + s[4] # s[4, 1] + s[4, 1] # s[1, 1, 1, 1] - s[4, 1] # s[1, 1, 1, 1, 1] + s[4, 1] # s[2, 1, 1, 1] + 2*s[4, 1] # s[2, 2, 1] + s[4, 1] # s[3, 1, 1] + s[4, 1] # s[3, 2] + s[5] # s[2, 1, 1] - s[5] # s[2, 1, 1, 1] + s[5] # s[3, 1, 1] + s[5] # s[3, 2]


    Substituting `q_n=1` (which should be equivalent to computing the plethysm on `X+1`)
    gives an e-positive expression (TODO: see why this is currently broken)::

        sage: res = tensor([s,e])( sum(c*tensor( [s[mu](s[1] + 1), s[nu]] ) for ((mu, nu), c) in Harm) )   # not tested
        sage: set(res.coefficients())                                                                      # not tested
        {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}
    """
    s = SymmetricFunctions(ZZ).s()
    ss = tensor([s,s])
    return ss.sum_of_terms([(Partition(mu), Partition(nu)), c]
                           for nu,d in harmonic_character_plain.dict().iteritems()
                           for mu,c in d.iteritems())

@cached_function
def harmonic_hilbert_series(n, r):
    return sum( harmonic_character(mu).expand(r, 'q') * StandardTableaux(mu).cardinality()
                for mu in Partitions(n) )

@cached_function
def harmonic_dimension(n, r):
    """
    Return the dimension of the harmonic space for r sets of n variables

    EXAMPLES::

        sage: [ harmonic_dimension(n, n-1) for n in range(7) ]
        [1, 2, 16, 400, 25769, 3751076]
    """
    f = sum( harmonic_character(mu) * StandardTableaux(mu).cardinality()
             for mu in Partitions(n) )
    # Do the expansion on the alphabet 1^r by hand ...
    fp = SymmetricFunctions(QQ).p()(f)
    return sum( c * r**len(nu) for nu, c in fp )

def truncate(f,d):
    return f.map_support_skip_none(lambda mu: mu if mu.size() < d else None)

def bitruncate(f,d):
    return f.map_support_skip_none(lambda (mu,nu): (mu,nu) if mu.size() < d and nu.size() < d else None)

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
