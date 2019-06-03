def factorise(f, n):
    var('q,t')
    SymmetricFunctions(QQ).s()
    supp = sorted(f.support())
    result = {}
    res = []
    for mu in Partitions(n):
        result[mu] = []
        for (a, b), c in zip(supp, f.coefficients()):
            if b == mu :
                result[mu] += [(a,c)]
    result2 = [(mu,sum(c*s(nu) for (nu,c) in result[mu])) for mu in result.keys()]
    for a, b in result2:
        print a, latex(b)
        #res += [[a,b]]
        
def test_quotient():
    P = DiagonalPolynomialRing(QQ, 3, 2, inert=1)
    W = DerivativeVandermondeSpaceWithInert(QQ, Diagram([(0,0),(1,0),(3,0)]))
    basis3 = W.basis_by_shape(Partition([3]))
    basis21 = W.basis_by_shape(Partition([2,1]))
    basis111 = W.basis_by_shape(Partition([1,1,1]))
    generators3 = {P.multidegree(P(gen)): [P(gen) for gen in g] for (d,g) in basis3.iteritems()}
    generators21 = {P.multidegree(P(gen)): [P(gen) for gen in g] for (d,g) in basis21.iteritems()}
    generators111 = {P.multidegree(P(gen)): [P(gen) for gen in g] for (d,g) in basis111.iteritems()}
    S3 = polarizationSpace(P, generators3)
    S21 = polarizationSpace(P, generators21)
    S111 = polarizationSpace(P, generators111)
    
    character_quotient(P, S3.basis(), 3)
    character_quotient(P, S21.basis(), 3)
    character_quotient(P, S111.basis(), 4)


def test():
    s = SymmetricFunctions(QQ).s()
    m = SymmetricFunctions(QQ).m()
    quotient=True
    mu = Diagram([(0,0),(2,0),(4,0)]) 
    nu = Partition([3])
    row_symmetry = None
    verbose = False
    n = mu.size()
    r = n-1
    charac = 0
    ss = SymmetricFunctions(QQ).s()

    H = DerivativeVandermondeSpaceWithInert(QQ, mu, inert=1, use_antisymmetry=False)
    basis = H.basis_by_shape(nu)

    P = DiagonalPolynomialRing(QQ, n, r, inert=1)
    operators = [functools.partial(P.symmetric_derivative, d=[d]) for d in range(1, H.degree_vandermonde()+1)]
    basis = quotiented_basis(P, basis, operators)
    generators = {P.multidegree(P(gen)): [P(gen) for gen in g] for (d,g) in basis.iteritems()}
    print "generators before polarization"
    for key, b in generators.iteritems():
        print key,b
    print
    operators = polarization_operators_by_multidegree(P, side='down', row_symmetry=row_symmetry, min_degree=1 if row_symmetry and row_symmetry!="permutation" else 0)
    print "----------------------------------------------------------------------------"
    S = polarizationSpace(P, generators, verbose=verbose, row_symmetry=row_symmetry)
    operators = [functools.partial(P.symmetric_derivative, d=[k if j==i1 else 0 for j in range(r)])  for k in range(1, H.degree_vandermonde()+1)for i1 in range(0,r)]
    #operators = [functools.partial(P.symmetric_derivative, d=[k if j==i1 else l if j==i2 else 0 for j in range(r)]) 
     #                                               for k in range(1, H.degree_vandermonde()+1) for l in range(1, H.degree_vandermonde()+1) 
     #                                               for i1 in range(0,r) for i2 in range(0,r)]
    print "generators after polarization before quotient"
    for key, b in S.basis().iteritems():
        print key,b
    print
    basis_pol = quotiented_basis(P, S.basis(), operators)
    print "after quotient"
    if S.basis() == basis_pol :
        print "toujours pareil"
    else:
        set1 = set(S.basis().items())
        set2 = set(basis_pol.items())
        print set1 ^ set2
    for degree, b in basis_pol.iteritems():
        if list(degree) == sorted(degree, reverse=True) :
            charac += s(sum(m(Partition(degree)) for p in b)).restrict_partition_lengths(r,exact=False)
    print charac
