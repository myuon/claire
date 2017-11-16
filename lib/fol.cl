# equivalence relation
axiom refl: Forall r. eq(r,r)
axiom subst: Forall a. Forall b. eq(a,b) ==> P(a) ==> P(b)

theorem sym: eq(r,s) ==> eq(s,r)
proof
  apply ImpR
  use subst []
  apply (ForallL [r]; ForallL [s])
  inst P [x => eq(x,r)]
  inst eq [(x,y) => eq(x,y)]
  apply (ImpL; PR 1; WR; I; ImpL)
  use refl []
  apply (ForallL [r])
  inst eq [(x,y) => eq(x,y)]
  apply (PR 1; WR; PL 0; WL; I; PL 0; WL; I)
qed

#axiom sym: eq(r,s) ==> eq(s,r)
axiom trans: eq(r,s) ==> eq(s,t) ==> eq(r,t)
axiom congr: eq(a,b) ==> eq(p(a),p(b))

# FORALL
axiom forallI: A(x) ==> FORALL(y,A(y))
axiom forallE: FORALL(x,A(x)) ==> A(t)

# TOP
axiom topI: FORALL(x,eq(x,x)) ==> TOP
axiom topE: TOP ==> FORALL(x,eq(x,x))

# BOTTOM
axiom bottomI: FORALL(x,x) ==> BOTTOM
axiom bottomE: BOTTOM ==> FORALL(x,x)

