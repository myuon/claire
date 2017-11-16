theorem id: P ==> P
proof
  apply (ImpR; I)
qed

# lemmas for LK
theorem deMorgan: (P /\ Q ==> Bottom) ==> ((P ==> Bottom) \/ (Q ==> Bottom))
proof
  apply (ImpR; ImpL; AndR)
    apply (PR 1; OrR1; ImpR; WR; I)
    apply (PR 1; OrR2; ImpR; WR; I)
  apply BottomL
qed

