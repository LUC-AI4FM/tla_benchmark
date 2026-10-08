MODULE NBAC
EXTENDS Naturals, Sequences, TLC

CONSTANT N \in Nat \ {0}

(* Types *)
VoteSet == {"YES","NO"}
DecisionSet == {"COMMIT", "ABORT", "NONE"}

Message == [from: 1..N, vote: VoteSet]
Msg(from, v) == [from |-> from, vote |-> v]

VARIABLES vote, decision, crashed, inbox, FD

(* Initialization *)
Init ==
  /\ vote \in [1..N -> VoteSet]
  /\ decision = [i \in 1..N |-> "NONE"]
  /\ crashed = [i \in 1..N |-> FALSE]
  /\ inbox = [i \in 1..N |-> <<>>]
  /\ FD = [i \in 1..N |-> {}]

(* Actions *)

SendProposal(i) ==
  /\ i \in 1..N
  /\ ¬crashed[i]
  /\ decision[i] = "NONE"
  /\ inbox' = [j \in 1..N |
        IF j ≠ i THEN Append(inbox[j], Msg(i, vote[i]))
        ELSE inbox[j]]
  /\ UNCHANGED <<vote, crashed, FD>>

ReceiveMsg(i) ==
  /\ i \in 1..N
  /\ inbox[i] ≠ <<>>
  /\ decision[i] = "NONE"
  /\ LET m == Head(inbox[i]) IN
       inbox' = [j \in 1..N |
                IF j = i THEN Tail(inbox[j])
                ELSE inbox[j]]
       decision' = [k \in 1..N |
                    IF k = i THEN
                      IF ∀ p \in 1..N : vote[p] = "YES" THEN "COMMIT"
                      ELSE "ABORT"
                    ELSE decision[k]]
  /\ UNCHANGED <<vote, crashed, FD>>

FDUpdate(i) ==
  /\ i \in 1..N
  /\ ∃ s ⊆ 1..N :
        FD' = [j \in 1..N |
                IF j = i THEN s
                ELSE FD[j]]
  /\ UNCHANGED <<vote, crashed, inbox, decision>>

Crash(i) ==
  /\ i \in 1..N
  /\ ¬crashed[i]
  /\ crashed' = [j \in 1..N | IF j = i THEN TRUE ELSE crashed[j]]
  /\ UNCHANGED <<vote, decision, inbox, FD>>

Next == ∨ i \in 1..N :
          SendProposal(i) \/ ReceiveMsg(i) \/ FDUpdate(i) \/ Crash(i)

(* Invariants *)

TypeInvariant ==
  /\ vote \in [1..N -> VoteSet]
  /\ decision \in [1..N -> DecisionSet]
  /\ crashed \in [1..N -> BOOLEAN]
  /\ inbox \in [1..N -> Seq(Message)]
  /\ FD \in [1..N -> SUBSET 1..N]

Validity ==
  ∀ i \in 1..N :
    decision[i] = "COMMIT" ⇒ (∀ j \in 1..N : vote[j] = "YES")

Spec == Init /\ [][Next]_vars

Safety == TypeInvariant /\ Validity

(*
THEOREM Spec => []Safety
*)

END MODULE