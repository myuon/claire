# equivalence relation
predicate eq(x,y)

axiom refl: Forall r. eq(r,r)
axiom subst: Forall a. Forall b. eq(a,b) ==> P(a) ==> P(b)

theorem sym: eq(r,s) ==> eq(s,r)
proof
  apply ImpR
  use subst []
  apply (ForallL [r], ForallL [s])
  inst P [x => eq(x,r)]
  inst eq [(x,y) => eq(x,y)]
  apply (ImpL, PR 1, WR, I, ImpL)
  use refl []
  apply (ForallL [r])
  inst eq [(x,y) => eq(x,y)]
  apply (PR 1, WR, PL 0, WL, I, PL 0, WL, I)
qed

theorem trans: eq(r,s) ==> eq(s,t) ==> eq(r,t)
proof
  apply (ImpR, ImpR)
  use subst []
  apply (ForallL [s], ForallL [t])
  inst P [x => eq(r,x)]
  apply (ImpL, PR 1, WR, PL 1, PL 0, WL, I)
  apply (ImpL, PR 1, WR, WL, I)
  apply (PL 0, WL, PL 0, WL, I)
qed


