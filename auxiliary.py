from sage.rings.qqbar import AlgebraicField
from sage.rings.rational_field import RationalField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.categories.homset import Hom

def extend_base(base_field, elements, name = 's'):
    #input: a base field K with a coerced embedding phi K -> QQbar and a list of elements = [a1, ..., an] of QQbar
    #output: the field L = K(a1,..., an) relative to K (so not absolute) with coercion into QQbar , the list of elements 
    #as they lie in L. 

    QQbar = AlgebraicField()
    QQ = RationalField()

    if not all([ w in QQbar for w in elements ]):
        raise ValueError('Not every element is defined over {}'.format(QQbar))

    if QQbar.coerce_map_from(base_field) == None: 
        QQbar.register_coercion(Hom(base_field,QQbar)[-1])

    adding_counter = 0
    elements_in_L = []
    while len(elements) != 0:
        a = elements[0]
        t = PolynomialRing(base_field, names = 't').gen()
        f_over_QQ = QQbar(a).minpoly()
        f_extended = f_over_QQ(t)
        #we have to pick the 'right' factor of the minimal polynomial of a. 
        #this is the factor which has the algebraic element as a root.
        for h in [factor[0] for factor in f_extended.factor()]:
            if h(a) == 0:
                minpoly = h
                break
        if minpoly.degree() == 1:
            elements_in_L.append(-minpoly(0))
        else:
            #If the factor of the minimal polynomial is not linear, we add the root to L
            #and embed L into QQbar where we send the newly adjoined root to a
            phi = QQbar.coerce_map_from(base_field)
            L = base_field.extension(minpoly, name + '{}'.format(adding_counter))
            if QQbar.coerce_map_from(L) == None:
                psi = Hom(L,QQbar)([a])
                QQbar.register_coercion(psi)

            adding_counter += 1
            elements_in_L = [L(e) for e in elements_in_L] + [L.gen()]
            base_field = L
        elements = elements[1:]
    return base_field, elements_in_L

def galois_orbit(j, F = RationalField()):
    #input: an algebraic element j and a base field (optional) which is embedded into 
    #QQbar via a coerced embedding or via phi
    #output: the galois orbit of j fixed by the base field in QQbar
    t = PolynomialRing(F,names = 't').gen()
    h = j.minpoly()(t)
    for f in [factor[0] for factor in h.factor()]:
        if f(j) == 0:
            poly = f
    return poly.roots(ring = AlgebraicField(), multiplicities = False)

def orbit_relative(j, L, K = RationalField()):
    #input: an element j of L. A field L with base field QQ and a subfield K of L.
    #output: an empty list if the Galois orbit of j is not contained in L and otherwise the orbit contained in L 
    t2 = PolynomialRing(L,names = 't').gen()
    h = j.minpoly()
    F = h(t2).factor()
    if not all([factor[1] == 1 for factor in F]):
        return []
    t = PolynomialRing(K, names = 't').gen()
    for F in h(t).factor():
        if F[0](j) == 0:
            poly = F[0]
            break
    return poly(t2).roots(ring = L, multiplicities = False)

def numbers_generating_residue(P):
    from sage.rings.polynomial.polydict import ETuple

    numbers = []
    x,y = P.parent().gens()

    while (
        P.derivative(y)(0,0) == 0 and 
        P.derivative(x)(0,0) == 0 and 
        P(0,0) == 0):
    
        vertices = P.dict().keys()

        leading_vert = min([v for v in vertices if v[0] == 0], key=lambda v: v[1])
        n = leading_vert[1]

        (a, b) = min([v for v in vertices if v[1] < n], key=lambda v: v[0])

        temp = RationalField()(a) / RationalField()(n - b)
        u, v = temp.numerator(), temp.denominator()

        t = PolynomialRing(AlgebraicField(), name='t').gen()

        f = sum(
            P.dict().get(ETuple((u * k, n - k*v)), 0) * t**k
            for k in range(n / v + 1)
        )

        f_rots = f.roots(multiplicities = False)


        if (v == 1 and len(f_rots) == 1):
            P = P(x, y + f_rots[0] * x**u)
        else: 
            P = (P(x**v, y * x**u + f_rots[0] * x**u) // x**(n * u))

        numbers.append(f_rots[0])

    return numbers
