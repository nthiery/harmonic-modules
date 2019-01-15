def symmetric_derivatives_x(P, max_degree) : 
    n = P._n
    return {-d: functools.partial(P.symmetric_derivative, d=[d])
            for d in range(1, max_degree+1)}

quotient = []
for op in sym_diff.itervalues():
     for b in basis.itervalues():
         for p in b:
             if op(P(p))!=0:
                 quotient += op(P(p))
    
generators = [P(p) for b in basis.itervalues() for p in b]
operators = [op for op in sym_diff.itervalues()]
S = Subspace(generators, operators)
# Pas une bonne solution car les generators sont aussi dans la base
# Or on ne les veut pas. Ecrire une nouvelle fonction qui calcule la base
# Sans les generators? 
