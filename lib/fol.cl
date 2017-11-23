Hs_file "lib/Commands.hs"

theorem Curry: (P ==> Q ==> R) ==> (P /\ Q ==> R)
proof
  apply (ImpR, ImpR, PL 1, ImpL, AndL1)
  assumption
  implyR
  apply (AndL2)
  assumption
qed

theorem Uncurry: (P /\ Q ==> R) ==> (P ==> Q ==> R)
proof
  apply (ImpR, ImpR, ImpR, PL 2)
  implyR
  apply (AndR)
  assumption
  assumption
qed

# equivalence relation
predicate eq: 'a => 'a => prop

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

Hs_file "lib/EqCommands.hs"

predicate T : bool => prop

# true, false
term true : bool
term false : bool

axiom bool_induction: P(true) ==> P(false) ==> P(b)

axiom trueT: T(true)
axiom falseT: T(false) ==> P

theorem T_true: T(p) ==> eq(p,true)
proof
  genR i[p]
  apply (ForallR b)
  use bool_induction {P: p => T(p) ==> eq(p,true)}
  implyL i[Curry {P: T(true) ==> eq(true,true), Q: T(false) ==> eq(false,true), R: T(b) ==> eq(b,true)}]
  implyR
  apply (AndR, ImpR)
  refl t[true]
  use falseT {P: eq(false,true)}
  apply I
qed

# and, or
term and : bool => bool => bool
term or : bool => bool => bool

axiom andI: T(P) ==> T(Q) ==> T(and(P,Q))
axiom andE1: T(and(P,Q)) ==> T(P)
axiom andE2: T(and(P,Q)) ==> T(Q)

axiom orI1: T(P) ==> T(or(P,Q))
axiom orI2: T(Q) ==> T(or(P,Q))
axiom orE: T(or(P,Q)) ==> (T(P) ==> T(R)) ==> (T(Q) ==> T(R)) ==> T(R)

# imp
term imp : bool => bool => bool

axiom impI: (T(P) ==> T(Q)) ==> T(imp(P,Q))
axiom impE: T(imp(P,Q)) ==> T(P) ==> T(Q)

theorem true_imp: eq(imp(true,q),q)
proof
  
qed

# forall, exist
term forall : bool => bool => bool
term exist : bool => bool => bool

axiom forallI: T(P(x)) ==> T(forall(x,P(x)))
axiom forallE: T(forall(x,P(x))) ==> T(P(t))

axiom existI: T(P(t)) ==> T(exist(x,P(x)))
axiom existE: T(exist(x,P(x))) ==> (T(P(x)) ==> T(Q)) ==> T(Q)

# not
term not : bool => bool
axiom not_def: eq(not(P),imp(P,false))

axiom abs: (T(not(P)) ==> T(false)) ==> T(P)

theorem not_true: eq(not(true),false)

