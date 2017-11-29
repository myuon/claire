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

definition {
  n[ iff: bool => bool => bool ];
  p[ eq(iff(P,Q), eqt(P,Q)) ];
}

axiom eqrefl: eq(eqt(t,t),true)
axiom eqsubst: eq(eqt(s,t),true) ==> P(s) ==> P(t)
axiom eqext: (Forall x. eq(eqt(f(x),g(x)),true)) ==> eq(eqt(x => f(x), x => g(x)),true)

axiom impI: (eq(eqt(P,true),true) ==> eq(eqt(Q,true),true)) ==> eq(imp(P,Q),true)
axiom mp: eq(imp(P,Q),true) ==> eq(P,true) ==> eq(Q,true)
axiom iff: eq(imp(imp(P,Q),imp(imp(Q,P),eqt(P,Q))),true)
axiom True_or_False: eq(or(eqt(P,true),eqt(P,false)),true)

# fundamental rules

## equality

theorem eqsym: eq(eqt(s,t),true) ==> eq(eqt(t,s),true)
proof
  apply ImpR
  implyL i[eqsubst {P: x => eq(eqt(x,s),true)}]
  implyR
  use eqrefl
  genR i[s]
  apply (ForallR t)
  apply I
qed

theorem eqssubst: eq(eqt(t,s),true) ==> P(s) ==> P(t)
proof
  genR i[s]
  genR i[t]
  apply (ForallR r, ForallR t)
  genR i[r]
  apply (ForallR s, ImpR)
  implyL i[eqsym]
  absL
  genR i[s]
  genR i[t]
  apply (ForallR r, ForallR t)
  genR i[r]
  apply (ForallR s)
  use eqsubst {P: x => P(x)}
  apply I
qed

