import "lib/preliminaries.cl"

# imply, eq
constant imp: bool => bool => bool
constant eqt: 'a => 'a => bool

# connectives & quantifiers
constant true: bool
constant false: bool
axiom true_def: eq(true, eqt(x => x, x => x))
axiom false_def: eq(false, p)

constant not: bool => bool
axiom not_def: eq(not(P),imp(P,false))

constant all: ('a => bool) => bool
axiom all_def: eq(all(P),eqt(P(x),true))

constant ex: ('a => bool) => bool
axiom ex_def: eq(all(P),not(ex(P)))

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
constant and : bool => bool => bool
constant or : bool => bool => bool

axiom andI: T(P) ==> T(Q) ==> T(and(P,Q))
axiom andE1: T(and(P,Q)) ==> T(P)
axiom andE2: T(and(P,Q)) ==> T(Q)

axiom orI1: T(P) ==> T(or(P,Q))
axiom orI2: T(Q) ==> T(or(P,Q))
axiom orE: T(or(P,Q)) ==> (T(P) ==> T(R)) ==> (T(Q) ==> T(R)) ==> T(R)

# imp
constant imp : bool => bool => bool

axiom impI: (T(P) ==> T(Q)) ==> T(imp(P,Q))
axiom impE: T(imp(P,Q)) ==> T(P) ==> T(Q)

theorem true_imp: eq(imp(true,q),q)
proof
  
qed

# forall, exist
constant forall : bool => bool => bool
constant exist : bool => bool => bool

axiom forallI: T(P(x)) ==> T(forall(x,P(x)))
axiom forallE: T(forall(x,P(x))) ==> T(P(t))

axiom existI: T(P(t)) ==> T(exist(x,P(x)))
axiom existE: T(exist(x,P(x))) ==> (T(P(x)) ==> T(Q)) ==> T(Q)

# not
constant not : bool => bool
axiom not_def: eq(not(P),imp(P,false))

axiom abs: (T(not(P)) ==> T(false)) ==> T(P)

theorem not_true: eq(not(true),false)
