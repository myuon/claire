# equivalence relation
axiom refl: forall r. eq(r,r)
axiom sym: forall r. forall s. eq(r,s) -> eq(s,r)
axiom trans: forall r. forall s. forall t. eq(r,s) -> eq(s,t) -> eq(r,t)
axiom congr: forall p. forall a. forall b. eq(a,b) -> eq(p(a),p(b))
axiom subst: forall p. forall a. forall b. eq(a,b) -> p(a) -> p(b)

# FORALL
axiom forallI: A(x) -> FORALL(y,A(y))
axiom forallE: FORALL(x,A(x)) -> A(t)

axiom topI: FORALL(x,eq(x,x)) -> TOP
axiom topE: TOP -> FORALL(x,eq(x,x))

axiom bottomI: FORALL(x,x) -> BOTTOM
axiom bottomE: BOTTOM -> FORALL(x,x)

