------------------------------ MODULE FastPaxos ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS AGENTS, COORDINATOR, VALUES

ASSUME
  /\ COORDINATOR \in AGENTS
  /\ AGENTS /= {}
  /\ VALUES /= {}

VARIABLES round, proposals, acceptances, committed

(* --------------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
  /\ round \in Nat
  /\ proposals \in [AGENTS -> (VALUES \/ {⊥})]
  /\ acceptances \in [AGENTS -> (VALUES \/ {⊥})]
  /\ committed \in VALUES \/ {⊥}

Init ==
  /\ round = 0
  /\ proposals = [a \in AGENTS |-> ⊥]
  /\ acceptances = [a \in AGENTS |-> ⊥]
  /\ committed = ⊥

(* --------------------------------------------------------------------------- *)
(* Helper definitions *)

Majority == (|AGENTS| div 2) + 1

CountProposed(v) ==
  |{a \in AGENTS : proposals[a] = v}|

(* --------------------------------------------------------------------------- *)
(* Actions *)

Propose(a, v) ==
  /\ a \in AGENTS
  /\ v \in VALUES
  /\ proposals' = [proposals EXCEPT ![a] = v]
  /\ UNCHANGED <<round, acceptances, committed>>

FastAccept ==
  LET vals == {v \in VALUES : CountProposed(v) >= Majority}
      chosen == IF vals = {} THEN ⊥ ELSE CHOOSE v \in vals
  IN /\ acceptances' = [a \in AGENTS |-> chosen]
     /\ UNCHANGED <<round, proposals, committed>>

CoordinatorSelect ==
  LET vals == {v \in VALUES : CountProposed(v) > 0}
      chosen == IF vals = {} THEN ⊥ ELSE CHOOSE v \in vals
  IN /\ acceptances' = [a \in AGENTS |-> chosen]
     /\ UNCHANGED <<round, proposals, committed>>

Commit ==
  LET vals == {v \in VALUES : ∀ a \in AGENTS : acceptances[a] = v}
      chosen == IF vals = {} THEN ⊥ ELSE CHOOSE v \in vals
  IN /\ committed' = chosen
     /\ UNCHANGED <<round, proposals, acceptances>>

Next ==
  \/ ∃ a \in AGENTS, v \in VALUES : Propose(a, v)
  \/ FastAccept
  \/ CoordinatorSelect
  \/ Commit

(* --------------------------------------------------------------------------- *)
(* Main specification and invariants *)

FastSpec == Init /\ [][Next]_<<round, proposals, acceptances, committed>>

FastTypeOK == TypeOK

FastNontriviality ==
  committed = ⊥ \/ ∃ a \in AGENTS : proposals[a] = committed

PaxosConsistency ==
  [] ((committed = ⊥) \/ (∃ v \in VALUES : committed = v /\ [](committed = v)))

=============================================================================