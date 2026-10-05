---------------------------- MODULE NBAC ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

States == {"YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH"}

Messages == {"YES", "NO"} \times Procs

VARIABLES pc, sent, rcvd, fd

vars == <<pc, sent, rcvd, fd>>

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ sent \subseteq Messages
    /\ rcvd \in [Procs -> SUBSET Messages]
    /\ fd \in [Procs -> BOOLEAN]

Init ==
    /\ pc \in [Procs -> {"YES", "NO"}]
    /\ sent = {}
    /\ rcvd = [p \in Procs |-> {}]
    /\ fd = [p \in Procs |-> FALSE]

InitAllYes ==
    /\ pc = [p \in Procs |-> "YES"]
    /\ sent = {}
    /\ rcvd = [p \in Procs |-> {}]
    /\ fd = [p \in Procs |-> FALSE]

Receive(p, msgs) ==
    /\ msgs \subseteq sent
    /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup msgs]

UpdateFD(p, newfd) ==
    /\ fd' = [fd EXCEPT ![p] = newfd]

UponYes(p) ==
    /\ pc[p] = "YES"
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ sent' = sent \cup {<<"YES", p>>}
    /\ \E msgs \in SUBSET sent : Receive(p, msgs)
    /\ \E newfd \in BOOLEAN : UpdateFD(p, newfd)

UponNo(p) ==
    /\ pc[p] = "NO"
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ sent' = sent \cup {<<"NO", p>>}
    /\ \E msgs \in SUBSET sent : Receive(p, msgs)
    /\ \E newfd \in BOOLEAN : UpdateFD(p, newfd)

ReceivedAllYes(p) ==
    \A q \in Procs : <<"YES", q>> \in rcvd[p]

UponSent(p) ==
    /\ pc[p] = "SENT"
    /\ \E msgs \in SUBSET sent : Receive(p, msgs)
    /\ \E newfd \in BOOLEAN :
        /\ UpdateFD(p, newfd)
        /\ IF newfd = FALSE /\ ReceivedAllYes(p)
           THEN pc' = [pc EXCEPT ![p] = "COMMIT"]
           ELSE pc' = [pc EXCEPT ![p] = "ABORT"]
    /\ sent' = sent

UponCrash(p) ==
    /\ pc[p] \in {"YES", "NO", "SENT"}
    /\ pc' = [pc EXCEPT ![p] = "CRASH"]
    /\ sent' = sent
    /\ rcvd' = rcvd
    /\ fd' = fd

Stutter(p) ==
    /\ pc[p] \in {"YES", "NO", "SENT"}
    /\ \E msgs \in SUBSET sent : Receive(p, msgs)
    /\ \E newfd \in BOOLEAN : UpdateFD(p, newfd)
    /\ pc' = pc
    /\ sent' = sent

Next ==
    \E p \in Procs :
        \/ UponYes(p)
        \/ UponNo(p)
        \/ UponSent(p)
        \/ UponCrash(p)
        \/ Stutter(p)

SendVote(p) ==
    \/ UponYes(p)
    \/ UponNo(p)

AttemptDecision(p) ==
    UponSent(p)

Fairness ==
    /\ \A p \in Procs : WF_vars(pc[p] \in {"YES", "NO"} /\ SendVote(p))
    /\ \A p \in Procs : WF_vars(pc[p] = "SENT" /\ AttemptDecision(p))

Spec == Init /\ [][Next]_vars /\ Fairness

AllInitiallyYes ==
    \A p \in Procs : pc[p] \in {"YES", "SENT", "ABORT", "COMMIT", "CRASH"} 
                     => (<<"YES", p>> \in sent \/ pc[p] \in {"YES", "CRASH"})

Validity ==
    \A p \in Procs : 
        pc[p] = "COMMIT" => 
            \A q \in Procs : <<"NO", q>> \notin sent

=========================================================================