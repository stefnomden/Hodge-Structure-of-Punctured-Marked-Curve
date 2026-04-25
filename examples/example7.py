#main example
#note how singular this curve is, for this one we need to extend the base field 
#so that the places at the singular points split

from sage.hodge_theory import MHS
from sage.hodge_theory import auxiliary

_.<a,b> = QQ[]

P = b^4 - ((1 - a)^6)^3 * (1/2 - a) * a^2

D = [(1,0), (1,0,0)]
E = [(0,0), (1/2, 0)]

HS = MHS.MixedHodgeStructure(P,D,E)

print('computing...')
HS.cohomology()
print('cohom done!')
HS.homology()
print('hom done!')
HS.period_matrix()
