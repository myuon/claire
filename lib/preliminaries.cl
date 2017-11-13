theorem id: a ==> a
proof
  apply (ImpR; I)
qed

# lemmas for LK
theorem deMorgan: Forall p. Forall q. (p /\ q ==> Bottom) ==> ((p ==> Bottom) \/ (q ==> Bottom))
proof
  apply (ForallR p; ForallR q)
  apply (ImpR; ImpL; AndR)
    apply (PR 1; OrR1; ImpR; WR; I)
    apply (PR 1; OrR2; ImpR; WR; I)
  apply BottomL
qed

