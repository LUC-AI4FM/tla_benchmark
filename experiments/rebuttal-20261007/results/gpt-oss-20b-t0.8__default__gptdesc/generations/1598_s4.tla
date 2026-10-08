MODULE FastMutualExclusion
   EXTENDS Naturals, FiniteSets

   CONSTANT N \in Nat

   VARIABLES x, y, b, S, cs

   Init ==
      /\ x = 0
      /\ y = 0
      /\ \A i \in 1..N : b[i] = FALSE
      /\ \A i \in 1..N : S[i] = {}
      /\ cs = {}

   SetFlag(i) ==
      /\ i \in 1..N
      /\ b[i] = FALSE
      /\ b'[i] = TRUE
      /\ UNCHANGED <<x, y, S, cs>>

   UnsetFlag(i) ==
      /\ i \in 1..N
      /\ b[i]
      /\ b'[i] = FALSE
      /\ UNCHANGED <<x, y, S, cs>>

   SetX(i) ==
      /\ i \in 1..N
      /\ x' = i
      /\ UNCHANGED <<b, y, S, cs>>

   SetY(i) ==
      /\ i \in 1..N
      /\ y' = i
      /\ UNCHANGED <<b, x, S, cs>>

   CanEnter(i) ==
      /\ b[i]
      /\ \A j \in 1..N : (j /= i) => NOT b[j]

   Entry(i) ==
      /\ i \in 1..N
      /\ CanEnter(i)
      /\ cs' = {i}
      /\ UNCHANGED <<b, x, y, S>>

   Exit(i) ==
      /\ i \in 1..N
      /\ i \in cs
      /\ cs' = {}
      /\ b'[i] = FALSE
      /\ UNCHANGED <<x, y, S>>

   Next == \/ \E i \in 1..N : SetFlag(i)
            \/ \E i \in 1..N : SetX(i)
            \/ \E i \in 1..N : SetY(i)
            \/ \E i \in 1..N : Entry(i)
            \/ \E i \in 1..N : Exit(i)

   Spec == Init /\ [][Next]_{<<x, y, b, S, cs>>} /\ WF_vars(Next)

   MutualExclusion ==
      \A i, j \in 1..N :
         (i /= j) => ~(i \in cs /\ j \in cs)

   Liveliness == []<>(cs # {})

END MODULE