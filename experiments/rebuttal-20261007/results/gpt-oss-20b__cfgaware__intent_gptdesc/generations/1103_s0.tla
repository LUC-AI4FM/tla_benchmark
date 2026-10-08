MODULE AtomicCommit

CONSTANT N

EXTENDS Naturals, TLC

(* ------------------------------------------------------------------ *)
(* Types and constants                                               *)
SUBSET Proc == 1..N
VoteVal      == {"YES","NO"}
DecisionVal  == {"Commit","Abort","Undecided"}

(* ------------------------------------------------------------------ *)
(* Variables                                                         *)
VARIABLES vote, alive, suspicion, received, decision, DeliveredMsgs

(* ------------------------------------------------------------------ *)
(* Type invariant                                                   *)
TypeOK ==
    /\ vote ∈ [Proc -> VoteVal]
    /\ alive ∈ [Proc -> BOOLEAN]
    /\ suspicion ∈ [Proc -> BOOLEAN]
    /\ received ∈ [Proc -> SUBSET Proc]
    /\ decision ∈ [Proc -> DecisionVal]
    /\ DeliveredMsgs ⊆ { <<i,j,v>> | i ∈ Proc /\ j ∈ Proc /\ v ∈ VoteVal }

(* ------------------------------------------------------------------ *)
(* Initial state                                                    *)
Init ==
    /\ vote \in [Proc -> VoteVal]          (* nondeterministic votes *)
    /\ alive   = [p ∈ Proc |-> TRUE]
    /\ suspicion = [p ∈ Proc |-> FALSE]
    /\ received  = [p ∈ Proc |-> {}]
    /\ decision  = [p ∈ Proc |-> "Undecided"]
    /\ DeliveredMsgs = {}

(* ------------------------------------------------------------------ *)
(* Actions                                                          *)

Send ==
    \E i ∈ Proc :
        /\ alive[i]
        /\ DeliveredMsgs' = DeliveredMsgs ∪ { <<i,j,vote[i]>> | j ∈ Proc \ {i} }
        /\ UNCHANGED <<vote, alive, suspicion, received, decision>>

Receive ==
    \E m ∈ DeliveredMsgs :
        /\ m[2] ∈ Proc
        /\ DeliveredMsgs' = DeliveredMsgs \ {m}
        /\ received' = [received EXCEPT ![m[2]] = @ ∪ {m[1]}]
        /\ UNCHANGED <<vote, alive, suspicion, decision>>

Crash ==
    \E i ∈ Proc :
        /\ alive[i]
        /\ alive' = [alive EXCEPT ![i] = FALSE]
        /\ UNCHANGED <<vote, suspicion, received, decision, DeliveredMsgs>>

FDChange ==
    \E i ∈ Proc :
        /\ suspicion' = [suspicion EXCEPT ![i] = NOT @]
        /\ UNCHANGED <<vote, alive, received, decision, DeliveredMsgs>>

DecideCommit ==
    \E j ∈ Proc :
        /\ alive[j]
        /\ decision[j] = "Undecided"
        /\ (\A i ∈ Proc : (suspicion[i] = FALSE) => vote[i] = "YES")
        /\ (\A i ∈ Proc \ {j} : (suspicion[i] = FALSE) => i ∈ received[j])
        /\ decision' = [decision EXCEPT ![j] = "Commit"]
        /\ UNCHANGED <<vote, alive, suspicion, received, DeliveredMsgs>>

DecideAbort ==
    \E j ∈ Proc :
        /\ alive[j]
        /\ decision[j] = "Undecided"
        /\ \E i ∈ Proc \ {j} : (suspicion[i] = FALSE) /\ i ∈ received[j] /\ vote[i] = "NO"
        /\ decision' = [decision EXCEPT ![j] = "Abort"]
        /\ UNCHANGED <<vote, alive, suspicion, received, DeliveredMsgs>>

Next ==
    \/ Send
    \/ Receive
    \/ Crash
    \/ FDChange
    \/ DecideCommit
    \/ DecideAbort

(* ------------------------------------------------------------------ *)
(* Safety invariants                                               *)

Agreement ==
    \A i,j ∈ Proc :
        /\ decision[i] <> "Undecided"
        /\ decision[j] <> "Undecided"
        => decision[i] = decision[j]

Validity ==
    \A i ∈ Proc :
        decision[i] = "Abort" => (\E j ∈ Proc : vote[j] = "NO")

Safety == Agreement /\ Validity

(* ------------------------------------------------------------------ *)
(* Liveness assumptions and guarantees                            *)

EventualAccuracy ==
    \A i ∈ Proc :
        alive[i] => ◇(suspicion[i] = FALSE)

Termination ==
    \A i ∈ Proc :
        alive[i] => ◇(decision[i] <> "Undecided")

Spec == Init /\ [][Next]_<<vote, alive, suspicion, received, decision, DeliveredMsgs>> /\ Safety

(* ------------------------------------------------------------------ *)
(* Optional LTL property combining assumptions and liveness       *)

LTLProp == EventualAccuracy => Termination

=============================================================================
