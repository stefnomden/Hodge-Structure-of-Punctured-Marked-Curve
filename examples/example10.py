from sage.hodge_theory import MHS
from sage.hodge_theory import auxiliary

_.<a,b> = QQ[]
P = b^3 - prod(a - i for i in range(3))
D = [(0,0),(1,0),(2,0)]

HS = MHS.MixedHodgeStructure(P, D = D)
HS.period_matrix()
