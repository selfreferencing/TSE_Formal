"""First Lyapunov coefficient of the coupled price-selection Hopf.

Concrete nonlinear coupled model in equilibrium coordinates (u=p-p*, w=x-x*):
    u' = -b u + c w                         (price adjusts to excess demand)
    w' = (xs+w)(1-xs-w)(a1 u + g1 w)        (2-type replicator; fitness diff linear)
Jacobian at origin = [[-b, c],[xs(1-xs)a1, xs(1-xs)g1]] = [[-b,c],[alpha,gamma]].
Hopf: gamma=b (trace 0), det = -b^2 - c*alpha > 0 (rotational, c*alpha<-b^2).
We compute the first Lyapunov coefficient l1 (Guckenheimer-Holmes); l1<0 => the
Hopf is SUPERCRITICAL, i.e. a STABLE limit cycle is born (the sustained boom-bust).
"""
import sympy as sp

u, w = sp.symbols('u w', real=True)
b, c, xs, a1, g1 = sp.symbols('b c xs a1 g1', real=True, positive=True)

# --- the coupled vector field (equilibrium at origin) ---
f1 = -b*u + c*w
f2 = (xs + w)*(1 - xs - w)*(a1*u + g1*w)

def l1_at(params):
    """Numeric first Lyapunov coefficient at a Hopf point given by `params`."""
    F1 = f1.subs(params); F2 = f2.subs(params)
    # Jacobian at origin
    J = sp.Matrix([[sp.diff(F1,u), sp.diff(F1,w)],
                   [sp.diff(F2,u), sp.diff(F2,w)]]).subs({u:0, w:0})
    J = sp.nsimplify(J); Jn = sp.matrix2numpy(J.evalf(), dtype=float)
    tr = float(J.trace()); det = float(J.det())
    assert abs(tr) < 1e-9, f"not a Hopf point: trace={tr}"
    assert det > 0, f"det must be >0: {det}"
    om = sp.sqrt(J.det())                     # onset frequency, eigenvalues +/- i*om
    # eigenvector v for eigenvalue +i*om ; build T=[Re v, -Im v] so T^{-1} J T = [[0,-om],[om,0]]
    lam = sp.I*om
    # (J - lam I) v = 0 -> from row1: (-b-lam) v1 + c v2 = 0 -> v = (c, b+lam)
    v = sp.Matrix([c.subs(params), (b.subs(params) + lam)])
    T = sp.Matrix.hstack(sp.re(v), -sp.im(v))
    Tinv = T.inv()
    # push the field into canonical coords: (xi,eta) with (u,w)=T (xi,eta)
    xi, eta = sp.symbols('xi eta', real=True)
    sub = {u: (T[0,0]*xi + T[0,1]*eta), w: (T[1,0]*xi + T[1,1]*eta)}
    Fvec = sp.Matrix([F1.subs(sub), F2.subs(sub)])
    G = Tinv * Fvec                            # (xi', eta') = G
    g_xi = sp.expand(G[0]); g_eta = sp.expand(G[1])
    # canonical linear part should be [[0,-om],[om,0]]; nonlinear parts f,g:
    fnl = sp.expand(g_xi - (-om*eta))
    gnl = sp.expand(g_eta - (om*xi))
    d = lambda e, *vs: sp.diff(e, *vs).subs({xi:0, eta:0})
    w_ = float(om)
    l1 = (sp.Rational(1,16)*(d(fnl,xi,3) + d(fnl,xi,eta,eta) + d(gnl,xi,xi,eta) + d(gnl,eta,3))
          + sp.Rational(1,16)/w_*(d(fnl,xi,eta)*(d(fnl,xi,2)+d(fnl,eta,2))
                                  - d(gnl,xi,eta)*(d(gnl,xi,2)+d(gnl,eta,2))
                                  - d(fnl,xi,2)*d(gnl,xi,2) + d(fnl,eta,2)*d(gnl,eta,2)))
    return float(sp.N(l1)), tr, det, float(sp.N(om))

# Hopf point: b=1, xs=1/2 (xs(1-xs)=1/4); gamma=b=1 => g1=4; alpha=-2 (c*alpha=-2<-1) => a1=-8; c=1.
pt = {b:1, c:1, xs:sp.Rational(1,2), g1:4, a1:-8}
l1, tr, det, om = l1_at(pt)
print(f"representative Hopf point b=1,c=1,alpha=-2,gamma=1,xs=1/2:")
print(f"  trace={tr:.3e}  det={det:.4f}  omega={om:.4f}")
print(f"  first Lyapunov coefficient l1 = {l1:.6f}  =>  {'SUPERCRITICAL (stable limit cycle)' if l1<0 else 'subcritical'}")

# scan a range of admissible Hopf points (vary alpha, c, xs) to check the sign is robust
import itertools
signs = []
for cval, aval, xsv in itertools.product([sp.Rational(1,2),1,2], [-2,-3,-5], [sp.Rational(1,3),sp.Rational(1,2),sp.Rational(2,3)]):
    bb=1
    if not (cval*aval < -bb**2):   # need c*alpha < -b^2
        continue
    g1v = sp.Rational(bb, xsv*(1-xsv))          # gamma=b
    a1v = sp.Rational(aval, xsv*(1-xsv))         # alpha=aval
    try:
        l1v,_,_,_ = l1_at({b:bb, c:cval, xs:xsv, g1:g1v, a1:a1v})
        signs.append((float(cval),float(aval),float(xsv),l1v))
    except AssertionError:
        pass
neg = sum(1 for *_,l in signs if l<0)
print(f"\nscan: {len(signs)} admissible Hopf points, {neg} supercritical (l1<0), "
      f"{len(signs)-neg} subcritical")
for cval,aval,xsv,l in signs:
    print(f"  c={cval:.2f} alpha={aval:.1f} xs={xsv:.2f}: l1={l:+.5f}")
