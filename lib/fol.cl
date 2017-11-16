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

## forall
#predicate forall(x,y)
#
#axiom forallI: eq(P(x),true) ==> forall(x,P(x))
#axiom forallE: forall(x,P(x)) ==> eq(P(t),true)
#
## true, false
#axiom true_def: eq(true, forall(x,eq(x,x)))
#axiom false_def: eq(false, forall(x,x))
#
## imp
#predicate imp(x,y)
#
#axiom impI: (eq(P,true) ==> eq(Q,true)) ==> imp(P,Q)
#axiom impE: imp(P,Q) ==> (eq(P,true) ==> eq(Q,true))
#
## not, and, or
#predicate not(x)
#predicate and(x,y)
#predicate or(x,y)
#
#axiom not_def: eq(not(P), imp(P,false))
#
## p/\q = ~(~p \/ ~q) = ~(p --> ~q)
#axiom and_def: eq(and(P,Q), not(imp(P,not(Q))))
#
#axiom or_def: eq(or(P,Q), not(and(not(P), not(Q))))
#
## exist
#predicate exist(x,y)
#
#axiom exist_def: eq(exist(x,P(x)), not(forall(x,P(x))))

