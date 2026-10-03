-------------------------------- MODULE OneStepConsensus --------------------------------
(***************************************************************************)
(* TLA+ specification of the one-step Byzantine consensus algorithm        *)
(* as described by Dobre and Suri (DSN 2006).                             *)
(* This folklore algorithm achieves consensus in a single communication    *)
(* step when conditions are favorable, tolerating Byzantine faults.        *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Naturals

CONSTANTS 
    N,          \* Total number of processes
    F,          \* Maximum number of Byzantine faults tolerated
    T           \* Threshold parameter for decision

VARIABLES
    proposed,       \* proposed[p] = value proposed by process p (0, 1, or -1 if none)
    sent,           \* sent[p] = value sent by process p (-1 if not yet sent)
    received,       \* received[p] = bag/multiset of values received by process p
    receivedCount0, \* receivedCount0[p] = count of 0s received by process p
    receivedCount1, \* receivedCount1[p] = count of 1s received by process p
    decided,        \* decided[p] = decision value of process p (-1 if undecided)
    faulty,         \* faulty[p] = TRUE if process p is Byzantine faulty
    faultyCount,    \* Current count of faulty processes
    pc              \* pc[p] = program counter for process p

\* Set of all processes
Procs == 1..N

\* Possible values that can be proposed
Values == {0, 1}

\* Special value indicating no decision yet or no proposal
NoValue == -1

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ proposed \in [Procs -> Values \cup {NoValue}]
    /\ sent \in [Procs -> Values \cup {NoValue}]
    /\ receivedCount0 \in [Procs -> 0..N]
    /\ receivedCount1 \in [Procs -> 0..N]
    /\ decided \in [Procs -> Values \cup {NoValue}]
    /\ faulty \in [Procs -> BOOLEAN]
    /\ faultyCount \in 0..N
    /\ pc \in [Procs -> {"init", "proposed", "sent", "decided", "faulty"}]

(***************************************************************************)
(* Initial state predicate                                                 *)
(***************************************************************************)
Init ==
    /\ proposed = [p \in Procs |-> NoValue]
    /\ sent = [p \in Procs |-> NoValue]
    /\ received = [p \in Procs |-> {}]
    /\ receivedCount0 = [p \in Procs |-> 0]
    /\ receivedCount1 = [p \in Procs |-> 0]
    /\ decided = [p \in Procs |-> NoValue]
    /\ faulty = [p \in Procs |-> FALSE]
    /\ faultyCount = 0
    /\ pc = [p \in Procs |-> "init"]

(***************************************************************************)
(* Initial state with all processes proposing 0                            *)
(***************************************************************************)
InitAll0 ==
    /\ proposed = [p \in Procs |-> 0]
    /\ sent = [p \in Procs |-> NoValue]
    /\ received = [p \in Procs |-> {}]
    /\ receivedCount0 = [p \in Procs |-> 0]
    /\ receivedCount1 = [p \in Procs |-> 0]
    /\ decided = [p \in Procs |-> NoValue]
    /\ faulty = [p \in Procs |-> FALSE]
    /\ faultyCount = 0
    /\ pc = [p \in Procs |-> "proposed"]

(***************************************************************************)
(* Initial state with all processes proposing 1                            *)
(***************************************************************************)
InitAll1 ==
    /\ proposed = [p \in Procs |-> 1]
    /\ sent = [p \in Procs |-> NoValue]
    /\ received = [p \in Procs |-> {}]
    /\ receivedCount0 = [p \in Procs |-> 0]
    /\ receivedCount1 = [p \in Procs |-> 0]
    /\ decided = [p \in Procs |-> NoValue]
    /\ faulty = [p \in Procs |-> FALSE]
    /\ faultyCount = 0
    /\ pc = [p \in Procs |-> "proposed"]

(***************************************************************************)
(* Action: Process p proposes a value v                                    *)
(***************************************************************************)
Propose(p, v) ==
    /\ pc[p] = "init"
    /\ ~faulty[p]
    /\ proposed' = [proposed EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "proposed"]
    /\ UNCHANGED <<sent, received, receivedCount0, receivedCount1, decided, faulty, faultyCount>>

(***************************************************************************)
(* Action: Process p sends its proposed value to all                       *)
(***************************************************************************)
Send(p) ==
    /\ pc[p] = "proposed"
    /\ ~faulty[p]
    /\ sent' = [sent EXCEPT ![p] = proposed[p]]
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<proposed, received, receivedCount0, receivedCount1, decided, faulty, faultyCount>>

(***************************************************************************)
(* Action: Process p receives a value v from process q                     *)
(* Correct processes send their proposed value; faulty may send anything   *)
(***************************************************************************)
Receive(p, q, v) ==
    /\ pc[p] = "sent"
    /\ ~faulty[p]
    /\ q \notin received[p]
    /\ \/ /\ ~faulty[q]
          /\ sent[q] = v
          /\ v \in Values
       \/ /\ faulty[q]
          /\ v \in Values
    /\ received' = [received EXCEPT ![p] = received[p] \cup {q}]
    /\ receivedCount0' = [receivedCount0 EXCEPT ![p] = 
                            IF v = 0 THEN receivedCount0[p] + 1 ELSE receivedCount0[p]]
    /\ receivedCount1' = [receivedCount1 EXCEPT ![p] = 
                            IF v = 1 THEN receivedCount1[p] + 1 ELSE receivedCount1[p]]
    /\ UNCHANGED <<proposed, sent, decided, faulty, faultyCount, pc>>

(***************************************************************************)
(* Action: Process p decides based on received messages                    *)
(* Decision rule: If received >= T messages with same value v, decide v    *)
(* Otherwise, decide default value (0)                                     *)
(***************************************************************************)
Decide(p) ==
    /\ pc[p] = "sent"
    /\ ~faulty[p]
    /\ decided[p] = NoValue
    /\ Cardinality(received[p]) >= N - F  \* Wait for enough messages
    /\ \/ /\ receivedCount1[p] >= T
          /\ decided' = [decided EXCEPT ![p] = 1]
       \/ /\ receivedCount0[p] >= T
          /\ receivedCount1[p] < T
          /\ decided' = [decided EXCEPT ![p] = 0]
       \/ /\ receivedCount0[p] < T
          /\ receivedCount1[p] < T
          /\ decided' = [decided EXCEPT ![p] = 0]  \* Default decision
    /\ pc' = [pc EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<proposed, sent, received, receivedCount0, receivedCount1, faulty, faultyCount>>

(***************************************************************************)
(* Action: Process p becomes Byzantine faulty                              *)
(***************************************************************************)
BecomeFaulty(p) ==
    /\ ~faulty[p]
    /\ faultyCount < F
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ faultyCount' = faultyCount + 1
    /\ pc' = [pc EXCEPT ![p] = "faulty"]
    /\ UNCHANGED <<proposed, sent, received, receivedCount0, receivedCount1, decided>>

(***************************************************************************)
(* Combined step for a process                                             *)
(***************************************************************************)
ProcessStep(p) ==
    \/ \E v \in Values : Propose(p, v)
    \/ Send(p)
    \/ \E q \in Procs : \E v \in Values : Receive(p, q, v)
    \/ Decide(p)
    \/ BecomeFaulty(p)

(***************************************************************************)
(* Next state relation                                                     *)
(***************************************************************************)
Next ==
    \E p \in Procs : ProcessStep(p)

(***************************************************************************)
(* Fairness condition: weak fairness on the main step                      *)
(***************************************************************************)
Fairness ==
    WF_<<proposed, sent, received, receivedCount0, receivedCount1, decided, faulty, faultyCount, pc>>(Next)

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<proposed, sent, received, receivedCount0, receivedCount1, decided, faulty, faultyCount, pc>> /\ Fairness

(***************************************************************************)
(* Alternative specifications with fixed initial proposals                 *)
(***************************************************************************)
SpecAll0 == InitAll0 /\ [][Next]_<<proposed, sent, received, receivedCount0, receivedCount1, decided, faulty, faultyCount, pc>> /\ Fairness

SpecAll1 == InitAll1 /\ [][Next]_<<proposed, sent, received, receivedCount0, receivedCount1, decided, faulty, faultyCount, pc>> /\ Fairness

(***************************************************************************)
(* SAFETY PROPERTIES                                                       *)
(***************************************************************************)

(***************************************************************************)
(* Agreement: No two correct processes decide differently                  *)
(***************************************************************************)
Agreement ==
    \A p, q \in Procs :
        /\ ~faulty[p]
        /\ ~faulty[q]
        /\ decided[p] \in Values
        /\ decided[q] \in Values
        => decided[p] = decided[q]

(***************************************************************************)
(* Validity: If all correct processes propose v, then any correct process  *)
(* that decides, decides v                                                 *)
(***************************************************************************)
Validity ==
    \A v \in Values :
        (\A p \in Procs : ~faulty[p] => proposed[p] = v)
        => (\A q \in Procs : (~faulty[q] /\ decided[q] \in Values) => decided[q] = v)

(***************************************************************************)
(* Integrity: A correct process decides at most once                       *)
(* (Encoded structurally: once in "decided" state, cannot decide again)    *)
(***************************************************************************)
Integrity ==
    \A p \in Procs :
        ~faulty[p] /\ pc[p] = "decided" => decided[p] \in Values

(***************************************************************************)
(* Non-triviality: Decision value must be a valid value                    *)
(***************************************************************************)
NonTriviality ==
    \A p \in Procs :
        decided[p] \in Values \cup {NoValue}

(***************************************************************************)
(* Bounded faults: Number of faulty processes never exceeds F              *)
(***************************************************************************)
BoundedFaults ==
    faultyCount <= F

(***************************************************************************)
(* Combined safety invariant                                               *)
(***************************************************************************)
Safety ==
    /\ TypeOK
    /\ Agreement
    /\ Validity
    /\ Integrity
    /\ NonTriviality
    /\ BoundedFaults

(***************************************************************************)
(* LIVENESS PROPERTIES                                                     *)
(***************************************************************************)

(***************************************************************************)
(* Termination: Every correct process eventually decides                   *)
(***************************************************************************)
Termination ==
    \A p \in Procs :
        ~faulty[p] => <>(decided[p] \in Values)

(***************************************************************************)
(* Progress: If a correct process proposes, it eventually decides          *)
(***************************************************************************)
Progress ==
    \A p \in Procs :
        (~faulty[p] /\ proposed[p] \in Values) ~> (decided[p] \in Values)

(***************************************************************************)
(* CONSTRAINTS for model checking                                          *)
(***************************************************************************)

\* Assumption: N > 3F for Byzantine consensus
Assumption == N > 3 * F

\* Assumption: Threshold T is meaningful
ThresholdAssumption == T > 0 /\ T <= N

=============================================================================