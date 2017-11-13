define top' = forall a. a -> a
define bottom' = forall a. a

theorem absurd: bottom' -> x
proof
qed

theorem id: a -> a
proof
  apply (ImpR; I)
qed

# equivalence relation
axiom refl: forall r. eq(r,r)
axiom sym: forall r. forall s. eq(r,s) -> eq(s,r)
axiom trans: forall r. forall s. forall t. eq(r,s) -> eq(s,t) -> eq(r,t)
axiom subst: forall p. forall a. forall b. eq(a,b) -> eq(p(a),p(b))

# lemmas for LK
theorem deMorgan: forall p. forall q. ~ (p /\ q) -> (~p \/ ~q)
proof
  apply (ForallR p; ForallR q)
  apply (ImpR; ImpL; AndR)
    apply (PR 1; OrR1; ImpR; WR; I)
    apply (PR 1; OrR2; ImpR; WR; I)
  apply BottomL
qed

#datatype nat = zero | succ(nat)
#axiom nat_ind: forall p. forall n. p(zero) -> (forall m. p(m) -> p(succ(m))) -> p(n)

#theorem nat_next: forall n. exist m. eq(n,succ(m))

