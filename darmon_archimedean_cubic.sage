from itertools import product,chain,izip,groupby,islice,tee,starmap

bk0 = Bessel(0,typ='K')
bk1 = Bessel(1,typ='K')

@cached_function
def get_ap(F,Ainv,P):
    if F == QQ:
        return EllipticCurve(Ainv).ap(P)
    try:
        return EllipticCurve(F.residue_field(P), Ainv).trace_of_frobenius()
    except ArithmeticError:
        # Bad reduction
        return EllipticCurve(Ainv).local_data(P).bad_reduction_type()

def get_apr(F,Ainv,P,r,N):
    if r == 0:
        return 1
    if P.divides(N):
        assert not (P**2).divides(N)
        return get_ap(F,Ainv,P)**r
    ap = get_ap(F,Ainv,P)
    if r == 1:
        return ap
    if F != QQ:
        NmP = P.norm()
    else:
        NmP = P
    return ap*get_apr(F,Ainv,P,r-1,N) - NmP*get_apr(F,Ainv,P,r-2,N)

def get_an(F,Ainv,n,N):
    if F != QQ:
        n = F.ideal(n)
    else:
        n = ZZ(n)
    return prod((get_apr(F,Ainv,P,r,N) for P,r in n.factor()),ZZ(1))

# returns w such that O_K = O_F +w·O_F
def module_generators(K):
    x=var('x')
    y=var('y')
    F=K.base_field()
    if F == QQ:
        return [1,K.maximal_order().ring_generators()[0]]
    f=F.polynomial()
    a=F.gen()
    g=K.relative_polynomial()
    b=K.gen()

    # Equivalent pari objects
    FP=F.pari_bnf().subst(x,y)
    fP=pari(f)
    KP=K.pari_rnf()
    gP=KP[0]
    BP=gp.rnfhnfbasis(FP,gP)

    E=[gp.matbasistoalg(FP,BP.vecextract(1)).lift(),gp.matbasistoalg(FP,BP.vecextract(2)).lift()]
    A=Matrix(F,2,2,0)
    for jj in range(2):
        for ii in [1,2]:
            tmp=E[jj][ii,1].Vec().sage()
            if(len(tmp)==2):
                A[ii-1,jj]=tmp[0]*a+tmp[1]
            else:
                A[ii-1,jj]=tmp[0]
    return (Matrix(K,1,2,[1,b])*A).list()

# returns a unit u in K such that norm_{K/F}(u)=1
def find_unit_K(K):
    F = K.base_field()
    units = K.units()
    for u in units:
        if u.minpoly().degree() == 2:
            norm_to_F = u.norm(F)
            if norm_to_F == 1:
                return u
            if F(norm_to_F).is_square():
                u = u/norm_to_F.sqrt()
                assert u.norm(F) == 1
                return u
            u = u^2
            assert (u/norm_to_F).norm(F) == 1
            return u/norm_to_F

# given beta in F returns the quadratic extension K obtained by adjoining sqrt{beta}; the generator of K is w such that O_K = O_F + w·O_F
def create_K(beta):
    F = beta.parent()
    y = F['y'].gen()
    Ktmp.<gtmp> = NumberField(y^2-beta)
    wlist = module_generators(Ktmp)
    assert wlist[0] == 1
    K.<w> = NumberField(wlist[1].minpoly())
    if w.is_integral() == False:
        print 'The  minimal polynomial of w is %s'%wlist[1].minpoly()
        print 'It seems that module_generators does not return an integer...'
        assert 0
    return K

def find_embedding_level_1(K):
    F = K.base_ring()
    w = K.gen()
    pol = w.minpoly()
    W = Matrix(F,2,2,[0,-pol[0],1,-pol[1]])
    assert W.minpoly() == pol
    return W

# W gives represents a maximal embedding of level 1 of K = F<w> into M_2(O_F); this function returns a matrix representing a maximal embedding of level N
# it might still have some bugs, but if it returns the result is correct
def find_embedding_level_N(W,N):
    F = W.base_ring()
    for n in range(0,N.norm()^2):
        for elt in F.elements_of_norm(n):
            M1 = Matrix(F,2,2,[1,elt,0,Ngen])
            M2 = Matrix(F,2,2,[Ngen,elt,0,1])
            for M in [M1*W*M1^-1,M1^-1*W*M1,M2^-1*W*M2,M2*W*M2^-1]:
                if all(a.is_integral() for a in M.list()) and M[1][0] in N:
                    assert M.minpoly() == W.minpoly()
                    return M
    return -1

# returns a unit u such that c = u+t*a for some integral element t
# returns 0 if not found
def is_represented_by_unit(c,a):
    F = a.parent()
    uF = F.units()[0]
    for i in range(0,a.norm()^2):
        units = [1,-1,uF^i,uF^-i]
        for u in units:
            if c-u in F.ideal(a):
                return u
    raise RuntimeError('is_represented_by_unit is returning 0')
    return 0

def fixed_point(g):
    a,b,c,d = g.list()
    tau = (a-d+((d-a)^2+4*b*c).sqrt())/(2*c)
    if tau.imag() < 0:
        tau = tau.conjugate()
    assert ((a*tau+b)/(c*tau+d)-tau).abs() < 10^-10
    return tau

# given a matrix gamma, returns the least i such that gamma^i has its upper left entry congruent to a unit mod N
def a_entry_represented_by_unit(g,Ngen):
    i = 1
    while True:
        a,b,c,d = (g^i).list()
        if is_represented_by_unit(a,Ngen):
            return i
        i += 1

# computes gamma_tau such that a is represented by a unit mod N (so, if necessary, we take powers of the unit in K that we use). Also returns a matrix U such that (U*gamma_tau)[0][0] is 1 mod N
def compute_gamma_tau(K,WN,N,force_Gamma_1 = False):
    uK = find_unit_K(K)
    gamma_tau = uK[0]+uK[1]*WN
    if force_Gamma_1:
        i = 1
        while True:
            a,b,c,d = (gamma_tau^i).list()
            if a-1 in N:
                print 'We are taking uK to the power %s'%i
                return gamma_tau^i
            i += 1
    exponent = a_entry_represented_by_unit(gamma_tau,N.gens_reduced()[0])
    gamma_tau = gamma_tau^exponent
    print 'We are taking uK to the power %s'%exponent
    a,b,c,d = gamma_tau.list()
    u = is_represented_by_unit(a,N.gens_reduced()[0])
    F = K.base_ring()
    if F.embeddings(RR)[0](u) < 0:
        gamma_tau = -gamma_tau
        u = -u
    return gamma_tau, Matrix(F,2,2,[u^-1,0,0,1])

# given a matrix in Gamma_1(N) with positive determinant returns a decomposition into elementary matrices
def factorize_in_Gamma_1_N(g,Ngen):
    a,b,c,d = g.list()
    F = Ngen.parent()
    # if F.real_embeddings()[0](g.det()) != 1:
    #     raise RuntimeError('Only implemented for matrices of determinant 1')
    u = is_represented_by_unit(c,a)
    t = (c-u)/a
    M1 = Matrix(F,2,2,[1,0,u*(a-1),1])
    M2 = Matrix(F,2,2,[1,u^-1,0,1])
    M3 = Matrix(F,2,2,[1,0,t*(a-1),1])*Matrix(F,2,2,[1,0,-c,1])
    M4 = M1*M2*M3*g
    dec = [M3^-1,M2^-1,M1^-1,M4]
    assert dec[0]*dec[1]*dec[2]*dec[3] == g
    for M in dec:
        assert M[1][0] in F.ideal(Ngen)
    return dec

def act_H_2(gg,tau,v = None):
    if v is not None:
        gg = gg.apply_morphism(v)
    a,b,c,d = gg.list()
    return (a*tau+b)/(c*tau+d)

def act_H_3(gg,x,y, v = None):
    if v is not None:
        gg = gg.apply_morphism(v)
    a,b,c,d = gg.list()
    den = (c*x+d).norm() +c.norm()*y^2
    new_y = (a*d-b*c).abs()*y/den
    new_x = ((a*x+b)*((c*x+d).conjugate())+a*c.conjugate()*y^2)/den
    return new_x, new_y

# this contains indefinite limits of the form tau (x) {Infinity -> G*Infinity}
# we just store tau and G
class IndefLimit(SageObject):
    def __init__(self,tau,G):
        self.tau = tau
        self.mat = G
    def convert_to_definite(self,N,v1):
        elt_mats = factorize_in_Gamma_1_N(self.mat,N.gens_reduced()[0])
        assert elt_mats[0]*elt_mats[1]*elt_mats[2]*elt_mats[3]==self.mat
        indef_limit = IndefLimit(self.tau,self.mat)
        def_limits = []
        for M in elt_mats:
            if M == 1:
                continue
            if M[1][0] == 0: # upper triangular
                tau, G = indef_limit.tau, indef_limit.mat
                indef_limit = IndefLimit(act_H_2(M^-1,tau,F.embeddings(RR)[0]),M^-1*G)
            elif M[0][1] == 0: # lower triangular
                tau, G = indef_limit.tau, indef_limit.mat
                indef_limit = IndefLimit(act_H_2(M^-1,tau,F.embeddings(RR)[0]),M^-1*G)
                # DL = DefLimit(tau,act_H_2(M^-1,tau,F.embeddings(RR)[0]),0,Infinity,0,Infinity)
                DL = DefLimit(tau,act_H_2(M^-1,tau,F.embeddings(RR)[0]),0,0,0,Infinity)
                def_limits.append(DL)
        assert indef_limit.mat == 1
        # this is for converting zero-infinity limits to limits in the upper-space
        limits = []
        Ngen = N.gens_reduced()[0] 
        N1 = v1(Ngen)
        WN = Matrix(N.ring(),2,2,[0,-1,Ngen,0])
        for lim in def_limits:
            # We identify the cusp at infinity in H3
            # with the point with (x,y)-coodinates (0,Infinity) 
            limits.append(DefLimit(lim.z0,lim.z1,0,1/N1.abs(),0,Infinity))
            zz0 = act_H_2(WN,lim.z0,F.embeddings(RR)[0])
            zz1 = act_H_2(WN,lim.z1,F.embeddings(RR)[0])
            xx1,yy1 = act_H_3(WN,CC(0),1/N1.abs(),v1)
            limits.append(DefLimit(zz0,zz1,0,Infinity,xx1,yy1))
        return limits

# the outer limits are complex number z0 (lower) and z1 (upper)
# x0 (complex) and y0 (real) are the lower interior limits
class DefLimit(SageObject):
    def __init__(self,z0,z1,x0,y0,x1,y1):
        self.z0, self.z1, self.x0, self.y0, self.x1, self.y1 = z0,z1,x0,y0,x1,y1
        self.vec = [[z0,z1],[x0,x1],[y0,y1]]
    def min_y(self):
        min_y = Infinity
        if min(self.vec[2]) < min_y:
            min_y = min(self.vec[2])
        return min_y
    def min_z(self):
        min_z = Infinity
        if min(self.vec[0][0].imag(),self.vec[0][1].imag()) < min_z:
            min_z = min(self.vec[0][0].imag(),self.vec[0][1].imag())
        return min_z


r'''
Returns exp(2 pi I z)
'''
def ee(z):
    if hasattr(z,'real_part'):
        zr,zi = z.real_part(),z.imag_part()
    else:
        zr,zi = RR(z),RR(0)
    zr = zr % 1
    twopizr = twopi*zr
    twopizi = twopi*zi
    return (-twopizi).exp() * CC(twopizr.cos(),twopizr.sin())

def H(t):
    r = RR(t.abs())
    K0 = bk0(RR(4 * pi * r))
    K1 = bk1(RR(4 * pi * r))
    rt = r * t
    return  matrix(CC,1,3,[-I/2 * rt * K1, r**2 * K0 ,I/2 * rt.conjugate() * K1])

r'''
Here, z is in the upper-half plane, x is complex, and y is positive real.
'''
def whittaker(alpha,delta,z,x,y):
    rat = alpha/delta
    ratvec = [emb(rat) for emb in alpha.parent().embeddings(CC)]
    return 1/ratvec[1].norm() * ee(-(ratvec[0] * z.conjugate() + ratvec[1] * x + ratvec[2] * x.conjugate())) * H(ratvec[1] * y)

def get_pows(i,ui):
    try:
        return ui[i]
    except IndexError:
        l = max(len(ui),1+i-len(ui))
        for j in range(l):
            ui.append(ui[1] * ui[-1])
        return ui[i]

def omega_E(E,z,x,y,norm_range,max_contribution,comparison = None):
    F = E.base_ring()
    N = E.conductor()
    delta = F.different().gens_reduced()[0]
    if F.embeddings(RR)[0](delta) < 0:
        delta = -delta
    u = F.units()[0]
    if F.embeddings(RR)[0](u) < 0:
        u = -u
    ui = [F(1),u]
    uiinv = [F(1),u**-1]
    res = matrix(CC,1,3,0)
    for n in norm_range:
        if n % 500 == 0:
            print 'n = %s'%n
            if comparison is not None:
                print sup_norm_mat(res-comparison)
        cont_n = matrix(CC,1,3,0)
        for alpha in F.elements_of_norm(n):
            cont_n = matrix(CC,1,3,0)
            an = get_an(F,E.ainvs(),alpha,N)
            i = 0
            while True:
                uialph = get_pows(i,ui) * alpha
                term = whittaker(uialph,delta,z,x,y)
                cont_n += term
                if sup_norm_mat(term) < max_contribution and i > 10:
                    break
                i += 1
            i = 1
            while True:
                uialph = get_pows(i,uiinv) * alpha
                term =  whittaker(uialph,delta,z,x,y)
                cont_n += term
                if sup_norm_mat(term) < max_contribution and i > 10:
                    break
                i += 1
            res += an * cont_n / F.embeddings(RR)[0](delta)
    return res

r'''
This corresponds to beta= dz/y, so it's not the "classical one".
'''
def automorphy_factor_H2(gamma,z):
    delta = gamma.determinant()
    F = gamma.parent().base_ring()
    v0 = F.embeddings(RR)[0]
    a,b,c,d = gamma.apply_morphism(v0).list()
    delta0 = v0(delta)
    eps = c*z + d
    return delta0 * eps.conjugate()**-2
    #return eps/eps.conjugate()

def automorphy_factor_H3(gamma,x,y):
    delta = gamma.determinant()
    F = gamma.parent().base_ring()
    v1 = F.embeddings(CC)[1] # A complex embedding!
    a1,b1,c1,d1 = gamma.apply_morphism(v1).list()
    r = c1*x + d1
    s = c1*y
    rconj = r.conjugate()
    sconj = s.conjugate()
    rn = RR(r * rconj)
    sn = RR(s * sconj)
    fact = 1/(rn+sn)
    if delta !=1:
        eps = v1(delta)/v1(delta).abs()
        fact *= matrix(CC,3,3,[eps,0,0,0,1,0,0,0,eps.conjugate()])
    # The following formula is sometimes wrong in the literature
    return fact * Matrix(CC,3,3,[rconj**2,-2*rconj*sconj,sconj^2,rconj*s,rn-sn,-r*sconj,s^2,2*r*s,r^2])

def J_factor(gamma,z,x,y):
    return automorphy_factor_H2(gamma,z) * automorphy_factor_H3(gamma,x,y)

def act_HH(gamma,z,x,y):
    F = gamma.parent().base_ring()
    v0,v1,v2 = F.embeddings(CC)
    assert v0(F.gen()).conjugate() == v0(F.gen())
    assert v1(F.gen()).conjugate() == v2(F.gen())
    gz = act_H_2(gamma,z,v0)
    gx,gy = act_H_3(gamma,x,y,v1)
    return gz,gx,gy

def sup_norm_mat(v):
    return max(a.abs() for a in v.list())

# returns the integral of one summand of the series between the limits (z_1,x1,y1) and (z_2,x1,infty) (al tanto: this term needs to be multiplied by a_(alpha)/N(alpha))
def int_term(z1,z2,x1,y1,alpha_over_delta_0,alpha_over_delta_1):
    ad0, ad1 = alpha_over_delta_0, alpha_over_delta_1
    ad2 = ad1.conjugate()
    K1 = bk1(RR(4 * pi * ad1.abs()*y1))
    ct = 1/(-8*pi**2*I*ad0*ad1.abs())
    exp_term = ee(-2*(ad1*x1).real())*(ee(-ad0*z2.conjugate())-ee(-ad0*z1.conjugate()))
    return ct*exp_term*y1*K1

# returns the integral of the modular form between the limits (z_1,x1,y1) and (z_2,x1,infty)
def int_to_infty(E,z1,z2,x1,y1,norm_range,max_contribution,comparison = None):
    if y1 == Infinity:
        return CC(0)
    F = E.base_ring()
    N = E.conductor()
    v0 = F.embeddings(RR)[0]
    v1 = F.embeddings(CC)[1]
    delta = F.different().gens_reduced()[0]
    if v0(delta) < 0:
        delta = -delta
    u = F.units()[0]
    if v0(u) < 0:
        u = -u
    ui = [F(1),u]
    uiinv = [F(1),u**-1]
    res = 0
    for n in norm_range:
        if n % 1000 == 0:
            print 'n = %s'%n
            print 'res = %s'%res
            if comparison is not None:
                print (res-comparison).abs()
        cont_n = 0
        for alpha in F.elements_of_norm(n):
            cont_n = 0
            an = get_an(F,E.ainvs(),alpha,N)
            i = 0
            while True:
                uialph = get_pows(i,ui) * alpha
                term = int_term(z1,z2,x1,y1,v0(uialph/delta),v1(uialph/delta))
                cont_n += term
                if term.abs() < max_contribution and i > 10:
                    break
                i += 1
            i = 1
            while True:
                uialph = get_pows(i,uiinv) * alpha
                term = int_term(z1,z2,x1,y1,v0(uialph/delta),v1(uialph/delta))
                cont_n += term
                if term.abs() < max_contribution and i > 10:
                    break
                i += 1
            res += an * cont_n / delta.norm()
    return res
