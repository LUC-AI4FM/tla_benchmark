\* Bakery mutual‑exclusion algorithm
MODULE Bakery

EXTENDS Naturals, Sequences

CONSTANTS NumProcs, MaxNum
ASSUME NumProcs >= 2 /\ MaxNum >= 1

Proc == 1 .. NumProcs

VARIABLES num, choosing, phase

(* Type invariant *)
TypeInvariant ==
    /\ num \in [Proc -> Nat]
    /\ choosing \in [Proc -> BOOLEAN]
    /\ phase \in [Proc -> {"choose", "wait", "cs"}]

Init ==
    /\ TypeInvariant
    /\ num = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]
    /\ phase = [i \in Proc |-> "choose"]

ChooseNumber(i) ==
  /\ i \in Proc
  /\ phase[i] = "choose"
  /\ LET maxVal == MAX( Seq({ num[j] : j \in Proc }) )
     IN  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
         /\ num' = [num EXCEPT ![i] = maxVal + 1]
         /\ phase' = [phase EXCEPT ![i] = "wait"]

Wait(i) ==
  /\ i \in Proc
  /\ phase[i] = "wait"
  /\ ∀ j \in Proc :
        (j = i \/ (choosing[j] = FALSE /\ (num[j] = 0 \/ num[j] > num[i] \/ (num[j] = num[i] /\ j > i))))
  /\ phase' = [phase EXCEPT ![i] = "cs"]

ExitCS(i) ==
  /\ i \in Proc
  /\ phase[i] = "cs"
  /\ num' = [num EXCEPT ![i] = 0]
  /\ phase' = [phase EXCEPT ![i] = "choose"]

Next == ∨ i \in Proc : (ChooseNumber(i) \/ Wait(i) \/ ExitCS(i))

vars == <<num, choosing, phase>>

Spec == Init /\ [][Next]_vars

Invariant ==
  ∀ i,j \in Proc :
    i # j => ~(phase[i] = "cs" /\ phase[j] = "cs")

Constraint ==
  ∀ i \in Proc : num[i] <= MaxNum

=============================================================================