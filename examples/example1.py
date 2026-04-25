from sage.hodge_theory import MHS
from sage.hodge_theory import auxiliary

#smooth example (not smooth at infinity)
_.<a,b> = QQ[]
f = a^6 + 1 
P = b^2 - f

q1 = (1, QQbar(sqrt(2)))
q1bar = (1, -QQbar(sqrt(2)))
q2 = (2, QQbar(sqrt(65))) 
q2bar = (2, -QQbar(sqrt(65))) 
q3 = (3, QQbar(sqrt(730)))
q3bar = (3, -QQbar(sqrt(730)))
q4 = (4, QQbar(sqrt(f(a=4))))
q4bar = (4, -QQbar(sqrt(f(a=4))))

D = [q1, q1bar, q2, q2bar, q3, q3bar, q4, q4bar]
D = [q1, q1bar]
E = [q4, q4bar]


HS = MHS.MixedHodgeStructure(P,D,E)

HS.homology()
HS.cohomology()
HS.period_matrix()
