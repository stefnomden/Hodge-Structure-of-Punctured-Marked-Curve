def check_dim(forms, functions):
    #input: a set of rational 1-forms and a finite subset of kC
    #output: the dimension of <forms> modulo <dfunctions>
    if forms == []:
        return 0
    kC = forms[0].parent().base_ring()
    x = kC.base_ring().gen()
    dx = kC(x).differential()
    big_space = [f.derivative() for f in functions] + [omega/dx for omega in forms]
    polyring = kC(x).element().list()[0].numerator().parent()
    D_x = lcm([polyring(lcm([a.denominator() for a in f.element().list()])) for f in big_space])
    big_space_cleared = [D_x * f for f in big_space]
    N = max( [max( [a.numerator().degree() for a in f.list()] ) for f in big_space_cleared] ) + 1

    to_be_matrix = []

    for f in big_space_cleared:
        row = []
        for a in f.list():
            coefficients = a.numerator().list()
            row.extend(coefficients + (N - len(coefficients)) * [0])
        to_be_matrix.append(row)
    A = matrix(to_be_matrix)

    #apply the equations dim(V cap W) = dim(V) + dim(W) - dim(V + W)
    #               and  dim(V/S) = dim(V) - dim(S)
    dim_of_sum = A.rank()
    dim_of_dLR = A[:len(functions)].rank()
    return dim_of_sum - dim_of_dLR
    


def basis_for_dR(P):
    #input: polynomial P in two variables over a finite extension of QQ.
    #output: a (nice) basis for the space H_{AdR}^1

    Field = P.parent().base_ring() #for now we pick QQ but ideally we would like to get the field over which P is defined
    a,b = P.parent().gens()
    K = FunctionField(Field, names = 'x')
    x = K.gen()
    Y = PolynomialRing(x.parent(), names = 'Y').gen()
    kC = K.extension(P(x,Y), names = 'y')
    y = kC.gen()
    coord_ring = kC.maximal_order()
    ring_at_oo = kC.maximal_order_infinite()
    genus = kC.genus()
    if genus == 0:
        return []
    dx = kC(x).differential()
    places_above_zero = list(map(lambda L : L[0].place(), coord_ring.ideal(x).factor()))
    places_above_infty = list(map(lambda L : L[0].place(), ring_at_oo.ideal(1/x).factor()))
    divx = kC(x).divisor_of_poles()
    div1_over_x = kC(1/x).divisor_of_poles()
    divy = kC(y).divisor_of_poles()
    canon_div_of_poles = divx + sum(divx.support())

    index = 1
    functions = [y^i for i in range(1,P.degree(b))]
    forms = [f*dx for f in functions]
    residues = []

    #calculate forms with residue 0 by calculating the kernel of the 'residue matrix'
    j = 0
    while len(residues) <= 2*genus or len(A.kernel().basis()) < 2*genus + 3:
        #the functions we generate only have poles above zero or infinity
        residues.append([r for p in places_above_zero + places_above_infty for r in forms[j].residue(p).list()])
        A = matrix(residues)
        #print(A.kernel().basis(),end = '\n\n')
        #generate more functions if we run out
        if j + 1 == len(functions): 
            functions.extend([y^i*x^(-index) for i in range(0,P.degree(b))] + [y^i*x^(index) for i in range(0,P.degree(b))])
            forms = [f*dx for f in functions]
            index += 1
        j += 1 

    zero_residue_forms = [sum([b*forms[i] for i,b in enumerate(v)]) for v in A.kernel().basis()]
    basis = []
    R = index*divx + (P.degree(b)-1)*divy + index*div1_over_x + canon_div_of_poles
    L_of_R = R.basis_function_space()
    k = 0
 
    #here we add elements to the basis and check its dimension until we get the expected dimension
    while len(basis) < 2*genus:
        #print('len(basis) = {}'.format(len(basis)))
        potential_new_basis = basis + [zero_residue_forms[k]]
        if check_dim(potential_new_basis,L_of_R) > len(basis):
            basis.append(zero_residue_forms[k])

        if k + 1 == len(zero_residue_forms) and len(basis) != 2*genus:
            #raise ValueError('fatal error... orbital space laser aimed at your location and charging')
            extra_residues_to_compute = 2*genus - len(basis)
            #print('we need {} more zero residue form!'.format(extra_residues_to_compute))
            for _ in range(extra_residues_to_compute):
                if j + 1 == len(functions):
                    functions.extend([y^i*x^(-index) for i in range(0,P.degree(b))] + [y^i*x^(index) for i in range(0,P.degree(b))])
                    forms = [f*dx for f in functions]
                    index += 1
                residues.append([r for p in places_above_zero + places_above_infty for r in forms[j].residue(p).list()])
                j += 1
            A = matrix(residues)
            zero_residue_forms = [sum([b*forms[i] for i,b in enumerate(v)]) for v in A.kernel().basis()]
            basis = []
            R = index*divx + (P.degree(b)-1)*divy + index*div1_over_x + canon_div_of_poles
            L_of_R = R.basis_function_space()
            k = -1
        
        #print('len(zero_residue_forms) = {}'.format(len(zero_residue_forms)))
        k += 1

    return basis

def reduction_non_res(basis, eta, check_residue = True):
    #input: a basis for the algebraic deRham of a curve and eta; a 1-form which has zero residue.
    #additionally, a boolean value determining whether it should be checked if the residue of the input is indeed zero
    #output: omega as an element of the basis, and f such that eta = omega + df
    kC = basis[0].parent().base_ring()
    if eta.parent().base_ring() != kC:
        raise ValueError('{} is not defined over the same curve as the given basis'.format(eta))
    x,y = kC.base_ring().gen() , kC.gen()
    dx = kC(x).differential()
    divx = kC(x).divisor_of_poles()
    eta_div_of_poles = (eta/dx).divisor_of_poles() + divx + sum(divx.support())
    if check_residue:
        for j in [eta.residue(p) for p in eta_div_of_poles.support()]:
            if j != 0:
                raise ValueError('{} does not have zero residue'.format(eta))
    
    set_of_oo_divs_basis = [(omega/dx).divisor_of_poles() + divx + sum(divx.support()) for omega in basis]
    support_of_R = list({p for omega in set_of_oo_divs_basis for p in omega.support()} | {p for p in eta_div_of_poles.support()})

    #find the divisor R which is defined to be R = max(omega1, ..., omegan, eta)
    R = sum([ max([div.dict().get(p,0) for div in set_of_oo_divs_basis + [eta_div_of_poles]])*p for p in support_of_R])
    R = R - sum(R.support())
    L_of_R = R.basis_function_space()
    
    #construct matrix and find kernel
    big_space = [omega/dx for omega in basis] + [f.derivative() for f in L_of_R] + [eta/dx]

    polyring = kC(x).element().list()[0].numerator().parent()
    D_x = lcm([polyring(lcm([a.denominator() for a in f.element().list()])) for f in big_space])
    big_space_cleared = [D_x * f for f in big_space]
    N = max( [max( [a.numerator().degree() for a in f.list()] ) for f in big_space_cleared] ) + 1

    to_be_matrix = []

    for f in big_space_cleared:
        row = []
        for a in f.list():
            coefficients = a.numerator().list()
            row.extend(coefficients + (N - len(coefficients)) * [0])
        to_be_matrix.append(row)
    
    A = matrix(to_be_matrix)
    
    relevant_vectors = [v for v in A.kernel().basis() if v[-1] != 0]

    v = relevant_vectors[0]

    omega = kC(-1/v[-1]) * sum([v[i]*omega for i,omega in enumerate(basis)]) 
    f     = kC(-1/v[-1]) * sum(v[i+len(basis)] * g for i,g in enumerate(L_of_R))

    return omega, f

    def galois_orbit(j, F = QQ):
    #input: an algebraic element j and a base field (optional) which is embedded into 
    #QQbar via a coerced embedding or via phi
    #output: the galois orbit of j fixed by the base field in QQbar
    _.<t> = F[]
    h = j.minpoly()(t)
    for f in [factor[0] for factor in h.factor()]:
        if f(j) == 0:
            poly = f
    return poly.roots(ring = QQbar, multiplicities = False)

def extend_base(base_field, elements, name = 's'):
    #input: a base field K with a coerced embedding phi K -> QQbar and a list of elements = [a1, ..., an] of QQbar
    #output: the field L = K(a1,..., an) relative to K (so not absolute) with coercion into QQbar , the list of elements 
    #as they lie in L. 

    if not all([ w in QQbar for w in elements ]):
        raise ValueError('Not every element is defined over {}}'.format(QQbar))

    if base_field.coerce_embedding() == None and base_field != QQ:
        raise ValueError('No natural embedding from the base field {} to {} found.'.format(base_field, QQbar))

    adding_counter = 0
    elements_in_L = []
    while len(elements) != 0:
        a = elements[0]
        _.<t> = base_field[]
        f_over_QQ = QQbar(a).minpoly()
        f_extended = f_over_QQ(t)
        #we have to pick the 'right' factor of the minimal polynomial of a. 
        #this is the factor which has the algebraic element as a root.
        for h in [factor[0] for factor in f_extended.factor()]:
            if h(a) == 0:
                minpoly = h
        if minpoly.degree() == 1:
            elements_in_L.append(-minpoly(0))
        else:
            #If the factor of the minimal polynomial is not linear, we add the root to L
            #and embed L into QQbar where we send the newly adjoined root to a
            phi = base_field.coerce_embedding()
            L = base_field.extension(minpoly, name + '{}'.format(adding_counter))
            if L.coerce_embedding() != None:
                pass
            elif (base_field == QQ) or (phi.codomain() != QQbar): 
                L._unset_coercions_used()
                L.register_embedding(Hom(L,QQbar)([a]))
            else: 
                L._unset_coercions_used()
                L.register_embedding(Hom(L,QQbar)([a], base_map = phi))
            adding_counter += 1
            elements_in_L = [L(e) for e in elements_in_L] + [L.gen()]
            base_field = L
        elements = elements[1:]
    return base_field, elements_in_L


def basis_non_residue(P,D):
    L_ab = P.parent()
    Field = L_ab.base_ring()
    
    checked = []
    orbits = []
    for p in D: 
        if p in checked:
            continue
        p_orbit = [(x_coord, y_coord) for x_coord in galois_orbit( QQbar(p[0]), F = Field ) for y_coord in galois_orbit(QQbar(p[1]), F = Field)]
        if len(p_orbit) != 1 and all(i in D for i in p_orbit):
            orbits.append(p_orbit)
            checked.extend(p_orbit)

    D_filt = [p for p in D if p not in checked]

    x_coords, y_coords = [L[0] for L in D_filt] , [L[1] for L in D_filt]
    Field2, coords = extend_base(Field, x_coords + y_coords) 

    if Field2 == QQ:
        Field2primitive = QQ
    else:
        Field2primitive = Field2.absolute_field('c')

    P_Field2 = P.parent().change_ring(base_ring = Field2)(P)
    P_primitive = P_Field2.parent().change_ring(base_ring = Field2primitive)(P_Field2)


    K.<x2> = FunctionField(Field2primitive)
    polyring = K.maximal_order()
    _.<Y> = K[]
    kC.<y2> = K.extension(P_primitive(x2,Y))
    OC = kC.maximal_order()

    Kbar.<x> = FunctionField(QQbar)
    L.<Y> = Kbar[]
    kCbar.<y> = Kbar.extension(P(Kbar(x),L(Y)))
    OCbar = kCbar.maximal_order()

    D_Field2 = [(coords[i], coords[i + len(D_filt)]) for i in range(len(D_filt))]
    D_primitive = [(Field2primitive(a), Field2primitive(b)) for (a,b) in D_Field2]

    places = [OC.ideal(OC(x2) - a, OC(y2) - b).divisor() for (a,b) in D_primitive]
    places.sort(key = lambda Div : -Div.degree())
    orbit_places = [p for O in orbits for p in kC.places_above( polyring.ideal(O[0][0].minpoly()(polyring.gen())).place())] #this needs some care, how do we know that the minimal polynomial does not split over Field2Primitive?

    dx = kC(x2).differential()
    dxbar = kCbar(x).differential()

    def convert(omega):
        elnew = 0
        for j,f in enumerate(list((omega/dx).element())):
            elnew += y^j * sum([x^i * QQbar(Field2(a)) for i,a in enumerate(f.numerator().list())])/sum([x^i * QQbar(Field2(a)) for i,a in enumerate(f.denominator().list())])
        return elnew * dxbar

    forms = []
    to_be_matrix = []
    places_bar_orbs = [p for O in orbits for (a,b) in O for p in OCbar.ideal(OCbar(x) - a, OCbar(y) - b).divisor().support()]
    places_bar_non_orbs = [p for (a,b) in D_filt for p in OCbar.ideal(OCbar(x) - a, OCbar(y) - b).divisor().support()]
    r = 0


    if len(orbit_places) != 0:
        for omega in (-sum(orbit_places)).basis_differential_space():
            omegabar = convert(omega)
            row = [omegabar.residue(p) for p in places_bar_orbs] + len(places_bar_non_orbs) * [0]
            if matrix(to_be_matrix + [row]).rank() > r:
                forms.append(omegabar)
                to_be_matrix.append(row)
                r += 1
    if len(places) != 0 and len(orbit_places) != 0:
        for omega in (-sum(orbit_places) - places[-1]).basis_differential_space():
            omegabar = convert(omega)
            row = [omegabar.residue(p) for p in places_bar_orbs] + (len(places_bar_non_orbs) - places[-1].degree()) * [0] + [omegabar.residue(p) for p in places_bar_non_orbs[-places[-1].degree():] ]
            if matrix(to_be_matrix + [row]).rank() > r:
                forms.append(omegabar)
                to_be_matrix.append(row)
                r += 1
    if len(places) > 1: 
        for omega in (-sum(places)).basis_differential_space():
            omegabar = convert(omega) 
            row = len(places_bar_orbs) * [0] + [omegabar.residue(p) for p in places_bar_non_orbs]
            if matrix(to_be_matrix + [row]).rank() > r:
                forms.append(omegabar)
                to_be_matrix.append(row)
                r += 1

    return forms, places_bar_orbs + places_bar_non_orbs

def reduction(eta, places, basis, residue_matrix = None):
    if residue_matrix == None:
        residue_matrix = matrix([[omega.residue(p) for p in places] for omega in basis])

    import time 
    start = time.time()
    v = vector([eta.residue(p) for p in places])
    end = time.time()
    print(end - start)

    non_residue_form = eta - sum([a * basis[i] for i,a in enumerate(residue_matrix.solve_left(v))])

    return non_residue_form, v
