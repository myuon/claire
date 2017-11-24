import "lib/preliminaries.cl"

# imply, eq
constant imp: bool => bool => bool
constant eqt: 'a => 'a => bool

# connectives & quantifiers
definition {
  n[ true: bool ];
  p[ eq(true, eqt(x => x, x => x)) ];
}

definition {
  n[ all: ('a => bool) => bool ];
  p[ eq(all(P), eqt(P,x => true)) ];
}

definition {
  n[ ex: ('a => bool) => bool ];
  p[ eq(ex(P), all(Q => imp(all(x => imp(P(x),Q)),Q))) ];
}

definition {
  n[ false: bool ];
  p[ eq(false, all(P => P)) ];
}

definition {
  n[ not: bool => bool ];
  p[ eq(not(P), imp(P,false)) ];
}

definition {
  n[ and: bool => bool => bool ];
  p[ eq(and(P,Q), all(R => imp(imp(P,imp(Q,R)),R))) ];
}

definition {
  n[ or: bool => bool => bool ];
  p[ eq(or(P,Q), all(R => imp(imp(P,R),imp(imp(Q,R),R)))) ];
}

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
