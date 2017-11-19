Hs_file "lib/Commands.hs"

predicate isnil: list(a) => bool

# equivalence relation
predicate eq: a => a => prop

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
predicate T : bool => prop

# true, false
term true
term false
term not(x)

axiom topI: T(true)
axiom bottomE: T(false) ==> T(P)

# and, or
term and(x,y)
term or(x,y)

axiom andI: T(P) ==> T(Q) ==> T(and(P,Q))
axiom andE1: T(and(P,Q)) ==> T(P)
axiom andE2: T(and(P,Q)) ==> T(Q)

axiom orI1: T(P) ==> T(or(P,Q))
axiom orI2: T(Q) ==> T(or(P,Q))
axiom orE: T(or(P,Q)) ==> (T(P) ==> T(R)) ==> (T(Q) ==> T(R)) ==> T(R)

# imp
term imp(x,y)

axiom impI: (T(P) ==> T(Q)) ==> T(imp(P,Q))
axiom impE: T(imp(P,Q)) ==> T(P) ==> T(Q)

# forall, exist
term forall(x,y)
term exist(x,y)

axiom forallI: T(P(x)) ==> T(forall(x,P(x)))
axiom forallE: T(forall(x,P(x))) ==> T(P(t))

axiom existI: T(P(t)) ==> T(exist(x,P(x)))
axiom existE: T(exist(x,P(x))) ==> (T(P(x)) ==> T(Q)) ==> T(Q)

# not
term not(x)

axiom not_def: eq(not(P),imp(P,false))

axiom abs: (T(not(P)) ==> T(false)) ==> T(P)

