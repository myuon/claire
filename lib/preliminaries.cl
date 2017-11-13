axiom bottom'E: bottom' -> (forall a. a)

theorem absurd': bottom' -> a
proof
  apply ImpR
  use bottom'E
  apply (ImpL; PR 1; WR; I; ForallL [a]; PL 0; WL; I)
qed

theorem id: a -> a
proof
  apply (ImpR; I)
qed

# lemmas for LK
theorem deMorgan: forall p. forall q. ~ (p /\ q) -> (~p \/ ~q)
proof
  apply (ForallR p; ForallR q)
  apply (ImpR; ImpL; AndR)
    apply (PR 1; OrR1; ImpR; WR; I)
    apply (PR 1; OrR2; ImpR; WR; I)
  apply BottomL
qed

