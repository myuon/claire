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

