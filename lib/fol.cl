Hs_file "lib/Commands.hs"

# equivalence relation
predicate eq(x,y)

axiom refl: eq(r,r)
axiom subst: eq(a,b) ==> P(a) ==> P(b)

theorem sym: eq(r,s) ==> eq(s,r)
proof
  apply ImpR
  apply Cut [Forall a. Forall b. eq(a,b) ==> eq(a,a) ==> eq(b,a)]
  use subst
  apply (ForallR a, ForallR b)
  inst P [x => eq(x,a)]
  assumption
  apply (ForallL [r], ForallL [s])
  apply ImpL
  assumption
  apply ImpL
  use refl
  assumption
  assumption
qed

theorem trans: eq(r,s) ==> eq(s,t) ==> eq(r,t)
proof
  apply (ImpR, ImpR)
  apply Cut [Forall a. Forall b. eq(a,b) ==> eq(r,a) ==> eq(r,b)]
  use subst
  inst P [x => eq(r,x)]
  apply (ForallR a, ForallR b)
  assumption
  apply (ForallL [s], ForallL [t])
  apply ImpL
  assumption
  apply ImpL
  assumption
  assumption
qed

# trueprop
term T(x)

# forall, true, false
term forall(x,y)
term true
term false

axiom T_def: eq(T(p),eq(p,true))

axiom forallI: T(P(x)) ==> T(forall(x,P(x)))
axiom forallE: T(forall(x,P(x))) ==> T(P(t))
axiom true_def: eq(true, forall(x,eq(x,x)))
axiom false_def: eq(false, forall(x,x))

# imp
term imp(x,y)

axiom impI: (T(P) ==> T(Q)) ==> T(imp(P,Q))
axiom impE: T(imp(P,Q)) ==> (T(P) ==> T(Q))

# not, and, or
term not(x)
term and(x,y)
term or(x,y)

axiom not_def: eq(not(P), imp(P,false))
axiom and_def: eq(and(P,Q), not(imp(P,not(Q))))
axiom or_def: eq(or(P,Q), not(and(not(P), not(Q))))

# exist
term exist(x,y)

axiom exist_def: eq(exist(x,P(x)), not(forall(x,P(x))))

