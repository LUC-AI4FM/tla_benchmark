---------------------------- MODULE folklore1s_byz ----------------------------
(* 
 * TLA+ specification of the folklore one-step consensus algorithm with Byzantine faults
 * Based on Dobre and Suri (DSN 2006)
 * 
 * The algorithm allows processes to reach consensus in a single communication step,
 * tolerating up to F Byzantine faults among N processes.
 *)

EXTENDS Integers, FiniteSets

CONSTANTS 
    N,      \* Total number of processes
    T,      \* Threshold parameter for decision
    F       \* Maximum number of Byzantine faults tolerated

VARIABLES
    pc,         \* Process control state: "init", "proposed", "decided", "faulty"
    proposal,   \* Initial proposal value for each process (0 or 1)
    decision,   \* Decision value for each process (0, 1, or -1 for undecided)
    sent0,      \* Number of 0-messages sent by correct processes
    sent1,      \* Number of 1-messages sent by correct processes
    rcvd0,      \* For each process: count of 0-messages received
    rcvd1,      \* For each process: count of 1-messages received
    faulty      \* Set of faulty processes

vars == <<pc, proposal, decision, sent0, sent1, rcvd0, rcvd1, faulty>>

Procs == 1..N
Values == {0, 1}

(* Type invariant *)
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

(* Initial state where all processes propose 0 *)
InitAll0 ==
    /\ pc = [p \in Procs |-> "init"]
    /\ proposal = [p \in Procs |-> 0]
    /\ decision = [p \in Procs |-> -1]
    /\ sent0 = 0
    /\ sent1 = 0
    /\ rcvd0 = [p \in Procs |-> 0]
    /\ rcvd1 = [p \in Procs |-> 0]
    /\ faulty = {}

(* Initial state where all processes propose 1 *)
InitAll1 ==
    /\ pc = [p \in Procs |-> "init"]
    /\ proposal = [p \in Procs |-> 1]
    /\ decision = [p \in Procs |-> -1]
    /\ sent0 = 0
    /\ sent1 = 0
    /\ rcvd0 = [p \in Procs |-> 0]
    /\ rcvd1 = [p \in Procs |-> 0]
    /\ faulty = {}

(* General initial state with arbitrary proposals *)
Init ==
    /\ pc = [p \in Procs |-> "init"]
    /\ proposal \in [Procs -> Values]
    /\ decision = [p \in Procs |-> -1]
    /\ sent0 = 0
    /\ sent1 = 0
    /\ rcvd0 = [p \in Procs |-> 0]
    /\ rcvd1 = [p \in Procs |-> 0]
    /\ faulty = {}

(* Propose action: a correct process broadcasts its proposal *)
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

(* Receive action: a correct process receives messages *)
Receive(p) ==
    /\ pc[p] \in {"proposed", "init"}
    /\ p \notin faulty
    \* Non-deterministically receive some subset of sent messages
    \* Byzantine processes can send arbitrary messages (up to F extra of each type)
    /\ \E new0 \in 0..(sent0 + F - rcvd0[p]):
       \E new1 \in 0..(sent1 + F - rcvd1[p]):
           /\ rcvd0[p] + new0 <= sent0 + F
           /\ rcvd1[p] + new1 <= sent1 + F
           /\ rcvd0' = [rcvd0 EXCEPT ![p] = rcvd0[p] + new0]
           /\ rcvd1' = [rcvd1 EXCEPT ![p] = rcvd1[p] + new1]
    /\ UNCHANGED <<pc, proposal, decision, sent0, sent1, faulty>>

(* Decide action: a correct process makes a decision based on received messages *)
Decide(p) ==
    /\ pc[p] = "proposed"
    /\ p \notin faulty
    \* Decision rule based on threshold T
    /\ \/ /\ rcvd0[p] >= T
          /\ rcvd1[p] < N - T
          /\ decision' = [decision EXCEPT ![p] = 0]
          /\ pc' = [pc EXCEPT ![p] = "decided"]
       \/ /\ rcvd1[p] >= T
          /\ rcvd0[p] < N - T
          /\ decision' = [decision EXCEPT ![p] = 1]
          /\ pc' = [pc EXCEPT ![p] = "decided"]
       \* If neither threshold is met, stay in proposed state (no decision yet)
    /\ UNCHANGED <<proposal, sent0, sent1, rcvd0, rcvd1, faulty>>

(* Become faulty: a process becomes Byzantine *)
BecomeFaulty(p) ==
    /\ p \notin faulty
    /\ Cardinality(faulty) < F
    /\ faulty' = faulty \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "faulty"]
    /\ UNCHANGED <<proposal, decision, sent0, sent1, rcvd0, rcvd1>>

(* Byzantine process sends arbitrary messages *)
ByzantineSend(p) ==
    /\ p \in faulty
    \* Byzantine process can increment sent counters arbitrarily
    /\ \/ /\ sent0' = sent0 + 1
          /\ sent1' = sent1
       \/ /\ sent1' = sent1 + 1
          /\ sent0' = sent0
       \/ /\ sent0' = sent0 + 1
          /\ sent1' = sent1 + 1
    /\ UNCHANGED <<pc, proposal, decision, rcvd0, rcvd1, faulty>>

(* Combined step action *)
Step ==
    \E p \in Procs:
        \/ Propose(p)
        \/ Receive(p)
        \/ Decide(p)
        \/ BecomeFaulty(p)
        \/ ByzantineSend(p)

(* Next state relation *)
Next == Step \/ UNCHANGED vars

(* Specification with weak fairness *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

(* Alternative specs for specific initial states *)
SpecAll0 == InitAll0 /\ [][Next]_vars /\ WF_vars(Step)
SpecAll1 == InitAll1 /\ [][Next]_vars /\ WF_vars(Step)

(* ====================