from sage.hodge_theory import MHS
from sage.hodge_theory import auxiliary

_.<a,b> = QQ[]

P = b^4 - 2*(a + 2) * b^2 + (a - 1) * (a - 4)

D = [(1,0), (4,0)]
E = [(0,sqrt(2)), (0,-sqrt(2))]

HS = MHS.MixedHodgeStructure(P, D = D, E = E)

HS.cohomology()
HS.homology()
HS.period_matrix()
