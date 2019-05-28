H = DerivativeVandermondeSpaceWithInert(QQ, Diagram([(0,0),(2,0),(4,0)]))
P = DiagonalPolynomialRing(QQ, 3, 2)
v = P(H.vandermonde())
d=4
n=3

X = P.variables()[0]
Y = P.variables()[1]
D = P._grading_set

s = SymmetricFunctions(QQ).s()

operators = {}

def make_deriv_comp_young3(X, Y, k, mu):
    def f(p):
        return apply_young_idempotent(sum(Y[i]*p.derivative(X[i],k) for i in range(0,len(X))), mu)
    return f

for nu in Partitions(3):
    operators[(D((-1,0)),nu)] = [make_deriv_comp_young(X[i], nu) for i in range(0,n)]
    operators[(D((-1,0)),nu)] += [make_deriv_comp_young2(X, 2, nu)]
    operators[(D((-2,0)),nu)] = [make_deriv_comp_young2(X, 3, nu)]
    
    operators[(D((0,-1)),nu)] = [make_deriv_comp_young(Y[i], nu) for i in range(0,n)]
    operators[(D((0,-1)),nu)] += [make_deriv_comp_young2(Y, 2, nu)]
    operators[(D((0,-2)),nu)] = [make_deriv_comp_young2(Y, 3, nu)]
    
    for k in range(1,d+1):
        operators[(D((-k,1)),nu)] = [make_deriv_comp_young3(X, Y, k, nu)]
        operators[(D((1,-k)),nu)] = [make_deriv_comp_young3(Y, X, k, nu)]
generators={(D((6,0)),Partition([1,1,1])):[v]}

basis = Subspace(generators=generators, operators=operators, add_degrees=add_degree_isotyp).basis()

for nu in Partitions(3):
    charac = 0
    print nu
    for key in basis.iterkeys():
        if nu == key[1]:
            charac += len(basis[key])*P.multipower(key[0])
    print charac
        
    charac = (s.from_polynomial(charac)).restrict_partition_lengths(2,exact=False)
    print charac
    print
            


