---------------------------- MODULE folklore_one_step ---------------------------
(* 
 * TLA+ specification of the folklore one-step consensus algorithm with Byzantine faults
 * Based on Dobre and Suri (DSN 2006)
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    N,          \* Total number of processes
    F,          \* Maximum number of Byzantine faulty processes
    T           \* Threshold parameter for decision

VARIABLES
    pc,         \* Process control state: "init", "proposed", "decided", "faulty"
    proposal,   \* Initial proposal value for each process (0 or 1)
    decision,   \* Decision value for each process (0, 1, or -1 for undecided)
    sent0,      \* Number of 0-messages sent
    sent1,      \* Number of 1-messages sent
    rcvd0,      \* Number of 0-messages received by each process
    rcvd1,      \* Number of 1-messages received by each process
    faulty      \* Set of faulty processes

vars == <<pc, proposal, decision, sent0, sent1, rcvd0, rcvd1, faulty>>

Procs == 1..N
Values == {0, 1}

TypeOK ==
    /\ pc \in [Procs -> {"init", "proposed", "decided", "faulty"}]
    /\ proposal \in [Procs -> Values]
    /\ decision \in [Procs -> {-1, 0, 1}]
    /\ sent0 \in 0..N
    /\ sent1 \in 0..N
    /\ rcvd0 \in [Procs -> 0..N]
    /\ rcvd1 \in [Procs -> 0..N]
    /\ faulty \subseteq Procs
    /\ Cardinality(faulty) <= F

(* Initial state with all processes proposing 0 *)
InitAll0 ==
    /\ pc = [p \in Procs |-> "init"]
    /\ proposal = [p \in Procs |-> 0]
    /\ decision = [p \in Procs |-> -1]
    /\ sent0 = 0
    /\ sent1 = 0
    /\ rcvd0 = [p \in Procs |-> 0]
    /\ rcvd1 = [p \in Procs |-> 0]
    /\ faulty = {}

(* Initial state with all processes proposing 1 *)
InitAll1 ==
    /\ pc = [p \in Procs |-> "init"]
    /\ proposal = [p \in Procs |-> 1]
    /\ decision = [p \in Procs |-> -1]
    /\ sent0 = 0
    /\ sent1 = 0
    /\ rcvd0 = [p \in Procs |-> 0]
    /\ rcvd1 = [p \in Procs |-> 0]
    /\ faulty = {}

(* General initial state - non-deterministic proposals *)
Init ==
    /\ pc = [p \in Procs |-> "init"]
    /\ proposal \in [Procs -> Values]
    /\ decision = [p \in Procs |-> -1]
    /\ sent0 = 0
    /\ sent1 = 0
    /\ rcvd0 = [p \in Procs |-> 0]
    /\ rcvd1 = [p \in Procs |-> 0]
    /\ faulty = {}

(* A correct process proposes its value by sending a message *)
Propose(p) ==
    /\ pc[p] = "init"
    /\ p \notin faulty
    /\ pc' = [pc EXCEPT ![p] = "proposed"]
    /\ IF proposal[p] = 0
       THEN /\ sent0' = sent0 + 1
            /\ sent1' = sent1
       ELSE /\ sent1' = sent1 + 1
            /\ sent0' = sent0
    /\ UNCHANGED <<proposal, decision, rcvd0, rcvd1, faulty>>

(* A process receives messages - models asynchronous message delivery *)
Receive(p) ==
    /\ pc[p] \in {"proposed", "init"}
    /\ p \notin faulty
    /\ \E delta0 \in 0..(sent0 - rcvd0[p]), delta1 \in 0..(sent1 - rcvd1[p]) :
        /\ delta0 + delta1 > 0  \* Receive at least one message
        /\ rcvd0' = [rcvd0 EXCEPT ![p] = rcvd0[p] + delta0]
        /\ rcvd1' = [rcvd1 EXCEPT ![p] = rcvd1[p] + delta1]
    /\ UNCHANGED <<pc, proposal, decision, sent0, sent1, faulty>>

(* A correct process decides based on received messages *)
Decide(p) ==
    /\ pc[p] = "proposed"
    /\ p \notin faulty
    /\ rcvd0[p] + rcvd1[p] >= N - F  \* Received enough messages
    /\ \/ /\ rcvd0[p] >= T           \* Decide 0 if enough 0-messages
          /\ decision' = [decision EXCEPT ![p] = 0]
       \/ /\ rcvd1[p] >= T           \* Decide 1 if enough 1-messages
          /\ decision' = [decision EXCEPT ![p] = 1]
       \/ /\ rcvd0[p] < T            \* No decision possible - default to 0
          /\ rcvd1[p] < T
          /\ decision' = [decision EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<proposal, sent0, sent1, rcvd0, rcvd1, faulty>>

(* A process becomes Byzantine faulty - can send arbitrary messages *)
BecomeFaulty(p) ==
    /\ p \notin faulty
    /\ Cardinality(faulty) < F
    /\ faulty' = faulty \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "faulty"]
    /\ UNCHANGED <<proposal, decision, sent0, sent1, rcvd0, rcvd1>>

(* A faulty process sends an arbitrary message *)
FaultySend(p) ==
    /\ p \in faulty
    /\ \/ /\ sent0' = sent0 + 1
          /\ sent1' = sent1
       \/ /\ sent1' = sent1 + 1
          /\ sent0' = sent0
    /\ UNCHANGED <<pc, proposal, decision, rcvd0, rcvd1, faulty>>

(* Main step combining all actions *)
Step ==
    \E p \in Procs :
        \/ Propose(p)
        \/ Receive(p)
        \/ Decide(p)
        \/ BecomeFaulty(p)
        \/ FaultySend(p)

Next == Step \/ UNCHANGED vars

(* Fairness condition *)
Fairness == WF_vars(Step)

Spec == Init /\ [][Next]_vars /\ Fairness

(* ====================