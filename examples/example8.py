#orbit at infinity example, 

from sage.hodge_theory import MHS

_.<a,b> = QQ[]

P = b^3 - a^3 - a - 1

_.<t> = QQbar[]
D = [(1,alpha,0) for alpha in (t^2 + t + 1).roots(multiplicities = False) + [1]]


HS = MHS.MixedHodgeStructure(P,D,[])

HS.cohomology_basis()
HS.homology()
HS.period_matrix().inverse()
