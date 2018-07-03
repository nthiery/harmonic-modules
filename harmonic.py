
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
                                  use_lie=True,
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

def truncate(f,d):
    return f.map_support_skip_none(lambda mu: mu if mu.size() < d else None)

def bitruncate(f,d):
    return f.map_support_skip_none(lambda (mu,nu): (mu,nu) if mu.size() < d and nu.size() < d else None)
