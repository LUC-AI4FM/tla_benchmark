---------------------------- MODULE OneStepConsensus ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

VARIABLES sentMsgs, rcvdMsgs, faulty, pc, decision

vars == <<sentMsgs, rcvdMsgs, faulty, pc, decision>>

Procs == 1..N

Values == {0, 1}

TypeOK ==
    /\ sentMsgs \in [Procs -> SUBSET (Procs \times Values)]
    /\ rcvdMsgs \in [Procs -> SUBSET (Procs \times Values)]
    /\ faulty \in SUBSET Procs
    /\ pc \in [Procs -> {"init", "proposed", "decided", "faulty"}]
    /\ decision \in [Procs -> Values \cup {-1}]

Init0 ==
    /\ sentMsgs = [p \in Procs |-> {}]
    /\ rcvdMsgs = [p \in Procs |-> {}]
    /\ faulty = {}
    /\ pc = [p \in Procs |-> "init"]
    /\ decision = [p \in Procs |-> 0]

Init1 ==
    /\ sentMsgs = [p \in Procs |-> {}]
    /\ rcvdMsgs = [p \in Procs |-> {}]
    /\ faulty = {}
    /\ pc = [p \in Procs |-> "init"]
    /\ decision = [p \in Procs |-> 1]

Init == Init0 \/ Init1

Propose(p, v) ==
    /\ pc[p] = "init"
    /\ p \notin faulty
    /\ sentMsgs' = [sentMsgs EXCEPT ![p] = sentMsgs[p] \cup {<<p, v>>}]
    /\ pc' = [pc EXCEPT ![p] = "proposed"]
    /\ UNCHANGED <<rcvdMsgs, faulty, decision>>

Receive(p, q, v) ==
    /\ pc[p] \in {"init", "proposed"}
    /\ p \notin faulty
    /\ <<q, v>> \in sentMsgs[q]
    /\ <<q, v>> \notin rcvdMsgs[p]
    /\ rcvdMsgs' = [rcvdMsgs EXCEPT ![p] = rcvdMsgs[p] \cup {<<q, v>>}]
    /\ UNCHANGED <<sentMsgs, faulty, pc, decision>>

ReceiveByzantine(p, q, v) ==
    /\ pc[p] \in {"init", "proposed"}
    /\ p \notin faulty
    /\ q \in faulty
    /\ <<q, v>> \notin rcvdMsgs[p]
    /\ rcvdMsgs' = [rcvdMsgs EXCEPT ![p] = rcvdMsgs[p] \cup {<<q, v>>}]
    /\ UNCHANGED <<sentMsgs, faulty, pc, decision>>

CountValue(p, v) ==
    Cardinality({m \in rcvdMsgs[p] : m[2] = v})

Decide(p) ==
    /\ pc[p] = "proposed"
    /\ p \notin faulty
    /\ Cardinality({m[1] : m \in rcvdMsgs[p]}) >= N - T
    /\ \/ /\ CountValue(p, 1) >= N - T
          /\ decision' = [decision EXCEPT ![p] = 1]
       \/ /\ CountValue(p, 0) >= N - T
          /\ decision' = [decision EXCEPT ![p] = 0]
       \/ /\ CountValue(p, 1) < N - T
          /\ CountValue(p, 0) < N - T
          /\ UNCHANGED decision
    /\ pc' = [pc EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<sentMsgs, rcvdMsgs, faulty>>

BecomeFaulty(p) ==
    /\ p \notin faulty
    /\ Cardinality(faulty) < F
    /\ faulty' = faulty \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "faulty"]
    /\ UNCHANGED <<sentMsgs, rcvdMsgs, decision>>

FaultySend(p, v) ==
    /\ p \in faulty
    /\ sentMsgs' = [sentMsgs EXCEPT ![p] = sentMsgs[p] \cup {<<p, v>>}]
    /\ UNCHANGED <<rcvdMsgs, faulty, pc, decision>>

Step ==
    \/ \E p \in Procs : \E v \in Values : Propose(p, v)
    \/ \E p \in Procs : \E q \in Procs : \E v \in Values : Receive(p, q, v)
    \/ \E p \in Procs : \E q \in Procs : \E v \in Values : ReceiveByzantine(p, q, v)
    \/ \E p \in Procs : Decide(p)
    \/ \E p \in Procs : BecomeFaulty(p)
    \/ \E p \in Procs : \E v \in Values : FaultySend(p, v)

Next == Step \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Agreement ==
    \A p, q \in Procs :
        /\ p \notin faulty
        /\ q \notin faulty
        /\ pc[p] = "decided"
        /\ pc[q] = "decided"
        /\ decision[p] \in Values
        /\ decision[q] \in Values
        => decision[p] = decision[q]

Validity ==
    \A p \in Procs :
        /\ p \notin faulty
        /\ pc[p] = "decided"
        /\ decision[p] \in Values
        => \E q \in Procs : q \notin faulty /\ decision[p] \in {m[2] : m \in sentMsgs[q]}

AllDecideOne ==
    \A p \in Procs : p \notin faulty => (pc[p] = "decided" /\ decision[p] = 1)

AllDecideZero ==
    \A p \in Procs : p \notin faulty => (pc[p] = "decided" /\ decision[p] = 0)

OneStep0_Ltl == <>[](AllDecideZero)

OneStep1_Ltl == <>[](AllDecideOne)

=============================================================================