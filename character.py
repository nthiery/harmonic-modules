#!/usr/bin/env python
# -*- coding: utf-8 -*-

import datetime
from diagonal_polynomial_ring import *
from derivative_space import *
from polarization_space import *


#################################################
# Characters of GL_r \times S_n modules
#################################################

def character(mu):
    if not isinstance(mu, Partitions):
        mu = Partition(mu)
    if mu.length() == 1:
        return harmonic_bicharacter(mu.size())
    else:
        return character_with_inert(mu)
        
        

##################################################
# Harmonic characters
##################################################

def harmonic_character(P, mu, verbose=False, row_symmetry=None, use_commutativity=False):
    """
    Return the `GL_r` character of the space of diagonal harmonic polynomials
    contributed by a given `S_n` irreducible representation.

    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ,5,4)
        sage: harmonic_character(P, Partition([3,2])) #not tested 
        # TODO NICOLAS : don't know how to correct the problem
        s[2] + s[2, 1] + s[2, 2] + s[3] + s[3, 1] + s[4] + s[4, 1] + s[5] + s[6]
    """
    mu = Partition(mu)
    n = P._n
    r = P._r
    if isinstance(P, DiagonalAntisymmetricPolynomialRing):
        antisymmetries = P._antisymmetries
        use_antisymmetry = True
    else:
        antisymmetries = None
        use_antisymmetry = False
    generators = [higher_specht(P, t, harmonic=True, use_antisymmetry=use_antisymmetry)
                  for t in StandardTableaux(mu)]
    F = polarizationSpace(P, mu, generators, verbose=verbose, 
                                     antisymmetries=antisymmetries, 
                                     row_symmetry=row_symmetry, 
                                     use_commutativity=use_commutativity)
    F.finalize()

    if row_symmetry != "euler+intersection":
        return F.hilbert_polynomial()
    # Otherwise:
    # The hilbert polynomial is expressed directly in terms of the
    # dimensions of the highest weight spaces; however the subspaces that
    # have been computed at this stage may include non highest weight
    # vectors.
    # We compute the intersection with the highest weight space,
    # i.e. the joint kernel of the f operators of the lie algebra
    # which are the polarization operators of degree 0 with i_2 < i_1
    operators = [functools.partial(P.polarization, i1=i1, i2=i2, d=1,
                                   antisymmetries=F._antisymmetries)
                 for i1 in range(1, r)
                 for i2 in range(i1)]
    return F._hilbert_parent({mu: len(annihilator_basis(basis._basis, operators, action=lambda b, op: op(b), ambient=self))
                              for mu, basis in F._bases.iteritems() if basis._basis})

# NICOLAS : Cette fonction est-elle devenue inutile ? (voir harmonic_bicharacter plus bas)
def harmonic_bicharacter_bis(P, verbose=False, row_symmetry=None, antisymmetries=None, use_lie=False):
    """
    Return the `GL_r-S_n` character of the space of diagonally harmonic polynomials

    EXAMPLES::

        sage: P = DiagonalPolynomialRing(QQ, 3, 2)
        sage: harmonic_bicharacter_bis(P) # not tested NICOLAS
        s[] # s[3] + s[1] # s[2, 1] + s[1, 1] # s[1, 1, 1] + s[2] # s[2, 1] + s[3] # s[1, 1, 1]

    """
    s = SymmetricFunctions(ZZ).s()
    if antisymmetries:
        use_antisymmetry = True
    else:
        use_antisymmetry = False
    H = DerivativeHarmonicSpace(QQ, P._n, use_antisymmetry=use_antisymmetry)
    generators = [H.basis_by_shape(nu) for nu in Partitions(P._n)]
    def char(mu):
        if verbose:
            print "%s:"%s(mu)
        r = tensor([polarizationSpace(P, generators, verbose=verbose,
                                                 row_symmetry=row_symmetry,
                                                ).hilbert_polynomial(),
                    s[mu]])
        return r
    # TODO Understand why this does not work in parallel
    #char = parallel()(char)
    #return sum( res[1] for res in char(Partitions(self._n).list()) )
    return sum(char(mu) for mu in Partitions(P._n))

def harmonic_character_plain(mu, verbose=False, parallel=False):
    """
    
    """
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
    result = harmonic_character(R, mu, verbose=progressbar,
                                  row_symmetry="permutation", #TODO NICOLAS : default parameter for row_symmetry ? 
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

# NICOLAS : Est-ce qu'il faut garder ça dans le code ? 
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

def harmonic_character_isotypic(mu):
    """
    Return the `GL_n` character of an `S_n` isotypic component in the
    diagonal harmonic polynomials

    Let `H` be the space of diagonal harmonic harmonic polynomials on
    `k\times n` variables, with `k` large enough.  Write its `GL_k
    \times S_n` bicharacter as `\sum f_\mu \otimes s_\mu`.  This
    computes `f_\mu`.

    EXAMPLES::

        sage: harmonic_character_isotypic([6])
        s[]
        sage: harmonic_character_isotypic([5, 1])
        s[1] + s[2] + s[3] + s[4] + s[5]
        sage: harmonic_character_isotypic([4, 2])
        s[2] + s[2, 1] + s[2, 2] + s[3] + s[3, 1] + s[3, 2] + 2*s[4] + 2*s[4, 1] + s[4, 2] + s[5] + s[5, 1] + 2*s[6] + s[6, 1] + s[7] + s[8]
        sage: harmonic_character_isotypic([4, 1, 1])
        s[1, 1] + s[2, 1] + s[3] + 2*s[3, 1] + s[3, 2] + s[3, 3] + s[4] + 2*s[4, 1] + s[4, 2] + 2*s[5] + 2*s[5, 1] + s[5, 2] + 2*s[6] + s[6, 1] + 2*s[7] + s[7, 1] + s[8] + s[9]
        sage: harmonic_character_isotypic([3, 3])
        s[2, 2] + s[2, 2, 1] + s[3] + s[3, 1] + s[3, 2] + s[4, 1] + s[4, 1, 1] + s[4, 2] + s[5] + s[5, 1] + s[5, 2] + s[6] + s[6, 1] + s[7] + s[7, 1] + s[9]
        sage: harmonic_character_isotypic([2, 2, 2])
        s[2, 2] + s[2, 2, 1] + s[3, 1, 1] + s[3, 1, 1, 1] + s[3, 2, 1] + s[3, 3, 1] + s[4, 1] + s[4, 1, 1] + 2*s[4, 2] + s[4, 2, 1] + s[4, 3] + s[4, 4] + s[5, 1] + 2*s[5, 1, 1] + 2*s[5, 2] + s[5, 2, 1] + s[5, 3] + s[6] + 2*s[6, 1] + s[6, 1, 1] + 2*s[6, 2] + s[6, 3] + 2*s[7, 1] + s[7, 1, 1] + s[7, 2] + s[8] + 2*s[8, 1] + s[8, 2] + s[9] + s[9, 1] + s[10] + s[10, 1] + s[12]
        sage: harmonic_character_isotypic([3, 1, 1, 1])
        s[1, 1, 1] + s[2, 1, 1] + s[3, 1] + 2*s[3, 1, 1] + s[3, 2] + s[3, 2, 1] + 2*s[3, 3] + s[3, 3, 1] + 2*s[4, 1] + 2*s[4, 1, 1] + 2*s[4, 2] + s[4, 2, 1] + 2*s[4, 3] + 3*s[5, 1] + 2*s[5, 1, 1] + 3*s[5, 2] + s[5, 2, 1] + 2*s[5, 3] + s[6] + 4*s[6, 1] + s[6, 1, 1] + 3*s[6, 2] + s[6, 3] + s[7] + 4*s[7, 1] + s[7, 1, 1] + 2*s[7, 2] + 2*s[8] + 3*s[8, 1] + s[8, 2] + 2*s[9] + 2*s[9, 1] + 2*s[10] + s[10, 1] + s[11] + s[12]
        sage: harmonic_character_isotypic([3, 2, 1])
        s[2, 1] + s[2, 1, 1] + s[2, 2] + s[2, 2, 1] + 2*s[3, 1] + 2*s[3, 1, 1] + 3*s[3, 2] + 2*s[3, 2, 1] + s[3, 3] + s[4] + 3*s[4, 1] + 2*s[4, 1, 1] + 4*s[4, 2] + s[4, 2, 1] + 2*s[4, 3] + 2*s[5] + 5*s[5, 1] + 2*s[5, 1, 1] + 4*s[5, 2] + s[5, 3] + 2*s[6] + 5*s[6, 1] + s[6, 1, 1] + 3*s[6, 2] + 3*s[7] + 4*s[7, 1] + s[7, 2] + 3*s[8] + 3*s[8, 1] + 2*s[9] + s[9, 1] + 2*s[10] + s[11]
        sage: harmonic_character_isotypic([2, 1, 1, 1, 1])
        s[1, 1, 1, 1] + s[2, 1, 1, 1] + s[3, 1, 1] + s[3, 1, 1, 1] + s[3, 2, 1] + s[3, 3, 1] + 2*s[4, 1, 1] + s[4, 1, 1, 1] + s[4, 2] + 2*s[4, 2, 1] + 2*s[4, 3] + 2*s[4, 3, 1] + s[4, 4] + 3*s[5, 1, 1] + s[5, 1, 1, 1] + s[5, 2] + 2*s[5, 2, 1] + 2*s[5, 3] + s[5, 3, 1] + s[5, 4] + s[6, 1] + 3*s[6, 1, 1] + 3*s[6, 2] + 2*s[6, 2, 1] + 3*s[6, 3] + s[6, 4] + 2*s[7, 1] + 3*s[7, 1, 1] + 3*s[7, 2] + s[7, 2, 1] + 2*s[7, 3] + 3*s[8, 1] + 2*s[8, 1, 1] + 3*s[8, 2] + s[8, 3] + 3*s[9, 1] + s[9, 1, 1] + 2*s[9, 2] + s[10] + 3*s[10, 1] + s[10, 2] + s[11] + 2*s[11, 1] + s[12] + s[12, 1] + s[13] + s[14]
        sage: harmonic_character_isotypic([2, 2, 1, 1])
        s[2, 1, 1] + s[2, 1, 1, 1] + s[2, 2, 1] + s[3, 1, 1] + s[3, 1, 1, 1] + s[3, 2] + 2*s[3, 2, 1] + s[3, 3] + s[3, 3, 1] + s[4, 1] + 3*s[4, 1, 1] + s[4, 1, 1, 1] + 2*s[4, 2] + 3*s[4, 2, 1] + 2*s[4, 3] + s[4, 3, 1] + s[4, 4] + 2*s[5, 1] + 3*s[5, 1, 1] + 4*s[5, 2] + 2*s[5, 2, 1] + 3*s[5, 3] + s[5, 4] + 3*s[6, 1] + 4*s[6, 1, 1] + 4*s[6, 2] + s[6, 2, 1] + 2*s[6, 3] + s[7] + 4*s[7, 1] + 2*s[7, 1, 1] + 4*s[7, 2] + s[7, 3] + s[8] + 4*s[8, 1] + s[8, 1, 1] + 2*s[8, 2] + 2*s[9] + 4*s[9, 1] + s[9, 2] + s[10] + 2*s[10, 1] + 2*s[11] + s[11, 1] + s[12] + s[13]
        sage: harmonic_character_isotypic([1, 1, 1, 1, 1, 1])
        s[1, 1, 1, 1, 1] + s[3, 1, 1, 1] + s[4, 1, 1, 1] + s[4, 2, 1] + s[4, 3, 1] + s[4, 4] + s[4, 4, 1] + s[5, 1, 1, 1] + s[5, 2, 1] + s[5, 3, 1] + s[6, 1, 1] + s[6, 1, 1, 1] + s[6, 2, 1] + s[6, 3] + s[6, 3, 1] + s[6, 4] + s[7, 1, 1] + s[7, 2] + s[7, 2, 1] + s[7, 3] + s[7, 4] + 2*s[8, 1, 1] + s[8, 2] + s[8, 2, 1] + s[8, 3] + s[9, 1, 1] + s[9, 2] + s[9, 3] + s[10, 1] + s[10, 1, 1] + s[10, 2] + s[11, 1] + s[11, 2] + s[12, 1] + s[13, 1] + s[15]
    """
    mu = tuple(mu)
    result = harmonic_character_plain(mu)
    S = SymmetricFunctions(ZZ)
    s = S.s()
    return s.sum_of_terms([Partition(d), c] for d,c in result.iteritems())

@parallel()
def harmonic_character_isotypic_paral(mu):
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
    for (((nu,),_), (result, t)) in harmonic_character_isotypic_paral((tuple(mu),) for mu in Partitions(n)):
        import tqdm
        tqdm.tqdm.write("\r%s\t("%Partition(nu)+str(t)[:-7]+"): %s"%
                                                     s.sum_of_terms([Partition(d), c]
                                                                    for d,c in result.iteritems()))

def harmonic_bicharacter(n):
    """
    
    """
    s = SymmetricFunctions(ZZ).s()
    ss = tensor([s,s])
    return ss.sum(tensor([harmonic_character_isotypic(mu), s.term(mu)])
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

def truncate(f,d):
    return f.map_support_skip_none(lambda mu: mu if mu.size() < d else None)

def bitruncate(f,d):
    return f.map_support_skip_none(lambda (mu,nu): (mu,nu) if mu.size() < d and nu.size() < d else None)


###########################################################################
# Characters for generalized version of Vandermonde with inert variables
###########################################################################

def character_with_inert(mu, inert=1, verbose=False, use_antisymmetry=False, row_symmetry=None, parallel=True): 
    """
    Return the complete bicharacter of the smallest submodule generated by $\Delta_{\mu}$
    and closed under partial derivatives and polarization operators for the double action
    of $GL_r \times S_n$. 
    The result is given as a sum of tensor product of Schur functions.
    
    EXAMPLES::        
        sage: character_with_inert(Partition([3]))
        s[] # s[3] + s[1] # s[2, 1] + s[1, 1] # s[1, 1, 1] + s[2] # s[2, 1] + s[3] # s[1, 1, 1]
        sage: character_with_inert(Partition([2,1]))
        s[] # s[2, 1] + s[1] # s[1, 1, 1]
        sage: character_with_inert(Partition([1,1,1]))
        s[] # s[1, 1, 1]

    """
    n = mu.size()
    r = mu.size()-1
    SymmetricFunctions(QQ).inject_shorthands(verbose=False)
    if parallel:
        charac = 0
        for (((_,nu),_),res) in character_by_isotypic_paral([(mu, nu) for nu in Partitions(n)]):
            if res:
                result = sum(dim*s(Partition(degrees)) for degrees,dim in res.iteritems())
                charac += tensor([result,s(nu)])
        return charac
    else:
        return character_by_isotypic(mu, inert=inert, use_antisymmetry=use_antisymmetry, row_symmetry=row_symmetry, verbose=verbose)
        
#def character_key(mu, **args):
#    return tuple(Composition(mu))
#def character_hash(mu):
#    return str(list(mu)).replace(" ","")[1:-1]
#character_with_inert = func_persist(character_with_inert,hash=character_hash,key=character_key)  

def character_by_isotypic(mu, inert=1, use_antisymmetry=False, row_symmetry=None, verbose=False):
    """
    Computes the sum of the bicharacters of $Gl_r times S_n$ of the 'nu'-isotypic 
    components of $S_n$ of the module generated by the generalized Vandermonde determinant 
    indexed by 'mu' and closed under derivation and polarization ofr each partition 'nu' of 
    the size of 'mu'.
    The resultat is given as a sum of tensor product of Schur functions. 
    
    INPUT : 'mu' -- a partition
    
    EXAMPLES::
        sage: character_by_isotypic(Partition([3]))
        s[] # s[3] + s[1] # s[2, 1] + s[1, 1] # s[1, 1, 1] + s[2] # s[2, 1] + s[3] # s[1, 1, 1]
        sage: character_by_isotypic(Partition([2,1]))
        s[] # s[2, 1] + s[1] # s[1, 1, 1]
        sage: character_by_isotypic(Partition([1,1,1]))
        s[] # s[1, 1, 1]
        sage: character_by_isotypic(Partition([2,2]))
        s[] # s[2, 2] + s[1] # s[2, 1, 1] + s[2] # s[1, 1, 1, 1]
    """
    n = mu.size()
    charac = 0
    for nu in Partitions(n):
        res = character_by_isotypic_plain(mu, nu, inert=inert, use_antisymmetry=use_antisymmetry, row_symmetry=row_symmetry, verbose=verbose)
        if res:
            result = sum(dim*s(Partition(degrees)) for degrees,dim in res.iteritems())
            charac += tensor([result,s(nu)])
    return charac

@parallel
def character_by_isotypic_paral(mu, nu):
    """
    See 'character_by_isotypic_plain'.
    This function is used for parallel computation. 
    
    INPUT: mu, nu -- partitions of the same size
    
    EXAMPLES::
        sage: SymmetricFunctions(QQ).inject_shorthands(verbose=False)
        sage: mu = Partition([2,1])
        sage: for nu in Partitions(3):
        ....:     character_by_isotypic_paral(mu, nu)
        0
        {(): 1}
        {(1,): 1}
        
        sage: mu = Partition([2,2])
        sage: for nu in Partitions(4):
        ....:     character_by_isotypic_paral(mu, nu)
        0
        0
        {(): 1}
        {(1,): 1}
        {(2,): 1}
    """
    if mu.size()==nu.size() :
        return character_by_isotypic_plain(mu, nu, inert=1, use_antisymmetry=True, row_symmetry="permutation", verbose=False)
    else :
        return "Error : mu and nu are not the same size."
    
def character_by_isotypic_plain(mu, nu, inert=1, use_antisymmetry=False, row_symmetry=None, verbose=False):
    """
    Computes the character of $Gl_r$ of the 'nu'-isotypic component of $S_n$ 
    of the module generated by the generalized Vandermonde determinant indexed by 
    'mu' and closed under derivation and polarization.

    INPUT:
        - `nu` -- a partition
        - `basis` -- a dict indexed by tuples of integers and partitions

    EXAMPLES::
        sage: mu = Partition([2,2])
        sage: for nu in Partitions(4):
        ....:     print (nu, character_by_isotypic_plain(mu, nu))    
        [4] 0
        [3, 1] 0
        [2, 2] {(): 1}
        [2, 1, 1] {(1,): 1}
        [1, 1, 1, 1] {(2,): 1}

    """
    n = mu.size()
    r = n-1
    charac = 0
    ss = SymmetricFunctions(QQ).s()
    
    H = DerivativeVandermondeSpaceWithInert(QQ, mu, inert=inert, use_antisymmetry=use_antisymmetry)
    basis = H.basis_by_shape(nu)
    
    if basis :
        if use_antisymmetry: 
            antisymmetries = antisymmetries_of_tableau(nu.initial_tableau())
            P = DiagonalAntisymmetricPolynomialRing(QQ, n, r, inert=1, antisymmetries=antisymmetries)
            generators = {P.multidegree(P(gen)): [reduce_antisymmetric_normal(P(gen), n, r+inert, antisymmetries) for gen in g] for (d,g) in basis.iteritems()}
        else :
            P = DiagonalPolynomialRing(QQ, n, r, inert=1)
            generators = {P.multidegree(P(gen)): [P(gen) for gen in g] for (d,g) in basis.iteritems()}
        S = polarizationSpace(P, generators, verbose=verbose, row_symmetry=row_symmetry)
        if row_symmetry=="permutation":
            for degree, b in S.basis().iteritems():
                charac += s(sum(m(Partition(degree)) for p in b)).restrict_partition_lengths(r,exact=False)
        else:
            for degree, b in S.basis().iteritems():
                charac += sum(P.multipower(degree) for p in b)
            charac = s(ss.from_polynomial(charac)).restrict_partition_lengths(r,exact=False)
    if charac:
        return {tuple(degrees): dim for degrees, dim in charac}
    else:
        return 0

def character_isotypic_plain_key(mu, nu, **args):
    return tuple(Composition(mu)), tuple(Composition(nu))
def character_isotypic_plain_hash(p_tuple):
    mu, nu = p_tuple
    return str(list(mu)).replace(" ","")[1:-1] + "_" + str(list(nu)).replace(" ","")[1:-1]
character_by_isotypic_plain = func_persist(character_by_isotypic_plain, hash=character_isotypic_plain_hash, key=character_isotypic_plain_key) 
