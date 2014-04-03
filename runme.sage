'''

  This file details the calculation of a Darmon point on a curve E
  which is defined over a cubic field F of signature (1,1).
  The point is defined over a quadratic extension K/F which is
  totally complex.

  The background for this computation is to be found in a paper by
  X.Guitart, M.Masdeu and H.Sengun "Darmon points in mixed signature".

'''

# Some initializations
prec_bits  = 80 # Working precision
CC = ComplexField(prec_bits)
RR = RealField(prec_bits)
I = CC(0,1)
assert I**2 == -1
pi = 4 * RR(1).arctan()
twopi = 2*pi

load 'darmon_archimedean_cubic.sage'

# construct F and E
x = QQ['x'].gen()
F.<r> = NumberField(x^3 - x^2 + 1)
v0 = F.embeddings(RR)[0]
v1 = F.embeddings(CC)[1]
E = EllipticCurve([r - 1,-r**2-1 ,r**2 - r,r**2,0  ])
N = E.conductor()
Ngen = N.gens_reduced()[0]
assert F.ideal(Ngen) == N
assert F.signature() == (1,1)
delta = F.different().gens_reduced()[0]

# We scale delta in this way so that v0(delta) is smaller.
# This helps in the integration, since the worst limits are the ones on the H2 side.
delta *= F.units()[0]^4

print 'Elliptic curve has conductor: %s'%N

# We have chosen an appropriate K so that E has a K-point of very small height:
y = QQ['y'].gen()
beta = -7*r^2 + 14*r - 11
x_coord = r-1
K.<w> = F.extension(y^2 + (r + 1)*y + 2*r^2 - 3*r + 3)
OK = K.maximal_order()
EK = E.base_extend(K)
P = EK.lift_x(x_coord)
print 'Known point is P=%s'%P

#### Below we compute the Darmon point

# Find the embedding
W1 = find_embedding_level_1(K)
WN = find_embedding_level_N(W1,N)
assert WN != -1

# Calculate gamma_tau and the the matrix resulting from the unit.
gamma_tau,U = compute_gamma_tau(K,WN,N)
assert gamma_tau.det() == 1 and gamma_tau[1][0] in N
assert (U*gamma_tau)[0][0]-1 in N
gamma_tau_0 = gamma_tau.apply_morphism(v0)
U_0 = U.apply_morphism(v0)
tau_0 = fixed_point(gamma_tau_0)

# Find the limits
indef_limit = IndefLimit(act_H_2(U_0,tau_0),U*gamma_tau)
def_limits = indef_limit.convert_to_definite(N,v1)

# Compute the integrals
J_tau = 0
minr = 1
maxr = 100000 # This will take a LONG time (a few hours)
for lim in def_limits:
    int_1 = int_to_infty(E, lim.z0, lim.z1, lim.x0, lim.y0, range(minr, maxr), 10**-40)
    int_2 = int_to_infty(E, lim.z0, lim.z1, lim.x1, lim.y1, range(minr, maxr), 10**-40)
    J_tau += (int_1 - int_2)

print 'Computed J_tau = %s'%J_tau
# J_tau should be about this (with norm up to 400000):
# J_tau = 0.00052812842341311719013530664351567588 + 0.0013607546066441620241871911551164971148788*I


# We compare the result with the precomputed point

EK = E.base_extend(K)
# w0 is an embedding of K extending v0, and v1 an embedding of K extending v1
for emb in K.embeddings(CC):
    if (v0(F.gen()) - emb(F.gen())).abs() < 2**(-prec_bits+10):
        w0 = emb
    if (v1(F.gen()) - emb(F.gen())).abs() < 2**(-prec_bits+10):
        w1 = emb

LK0 = EK.period_lattice(w0)
LK1 = EK.period_lattice(w1)
B0 = LK0.basis(prec_bits)
B1 = LK1.basis(prec_bits)
# The complex period
Omega_E = (B1[0].conjugate()*B1[1]).imag().abs()
z_P = LK0.elliptic_logarithm(EK(P), prec_bits)

# It is unclear to us why the factors of 2*pi*I and the 23 appears in the formula.
# It may be connected to the BSD formula
z_tau = (2*pi*I)**3 * CC(23).sqrt()/Omega_E *J_tau
print gp.lindep([z_tau,z_P,B0[0],B0[1]],19)
