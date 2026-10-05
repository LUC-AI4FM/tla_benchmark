------------------------------ MODULE NBAC ------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

States == {"YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH"}

VARIABLES pc, sent, rcvd, fd

vars == <<pc, sent, rcvd, fd>>

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ sent \subseteq (Procs \times {"YES", "NO"})
    /\ rcvd \in [Procs -> SUBSET (Procs \times {"YES", "NO"})]
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

UpdateFD(p, fdVal) ==
    /\ fd' = [fd EXCEPT ![p] = fdVal]

UponYes(p) ==
    /\ pc[p] = "YES"
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ sent' = sent \cup {<<p, "YES">>}
    /\ \E msgs \in SUBSET sent : Receive(p, msgs)
    /\ \E fdVal \in BOOLEAN : UpdateFD(p, fdVal)

UponNo(p) ==
    /\ pc[p] = "NO"
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ sent' = sent \cup {<<p, "NO">>}
    /\ \E msgs \in SUBSET sent : Receive(p, msgs)
    /\ \E fdVal \in BOOLEAN : UpdateFD(p, fdVal)

ReceivedAllYes(p) ==
    /\ \A q \in Procs : <<q, "YES">> \in rcvd[p]

ReceivedNo(p) ==
    \E q \in Procs : <<q, "NO">> \in rcvd[p]

UponSent(p) ==
    /\ pc[p] = "SENT"
    /\ \E msgs \in SUBSET sent : Receive(p, msgs)
    /\ \E fdVal \in BOOLEAN : UpdateFD(p, fdVal)
    /\ sent' = sent
    /\ IF /\ ~fd'[p]
          /\ ReceivedAllYes(p) \/ (\A q \in Procs : <<q, "YES">> \in (rcvd[p] \cup msgs))
       THEN pc' = [pc EXCEPT ![p] = "COMMIT"]
       ELSE IF fd'[p] \/ ReceivedNo(p) \/ (\E q \in Procs : <<q, "NO">> \in (rcvd[p] \cup msgs))
            THEN pc' = [pc EXCEPT ![p] = "ABORT"]
            ELSE pc' = pc

UponSentDecide(p) ==
    /\ pc[p] = "SENT"
    /\ \E msgs \in SUBSET sent :
        /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup msgs]
        /\ \E fdVal \in BOOLEAN :
            /\ fd' = [fd EXCEPT ![p] = fdVal]
            /\ LET newRcvd == rcvd[p] \cup msgs
                   allYes == \A q \in Procs : <<q, "YES">> \in newRcvd
                   hasNo == \E q \in Procs : <<q, "NO">> \in newRcvd
               IN IF ~fdVal /\ allYes
                  THEN pc' = [pc EXCEPT ![p] = "COMMIT"]
                  ELSE IF fdVal \/ hasNo
                       THEN pc' = [pc EXCEPT ![p] = "ABORT"]
                       ELSE pc' = pc
    /\ sent' = sent

UponCrash(p) ==
    /\ pc[p] \notin {"ABORT", "COMMIT", "CRASH"}
    /\ pc' = [pc EXCEPT ![p] = "CRASH"]
    /\ sent' = sent
    /\ rcvd' = rcvd
    /\ fd' = fd

DoNothing(p) ==
    /\ pc[p] \notin {"ABORT", "COMMIT", "CRASH"}
    /\ \E msgs \in SUBSET sent : Receive(p, msgs)
    /\ \E fdVal \in BOOLEAN : UpdateFD(p, fdVal)
    /\ pc' = pc
    /\ sent' = sent

Step(p) ==
    \/ UponYes(p)
    \/ UponNo(p)
    \/ UponSentDecide(p)
    \/ UponCrash(p)
    \/ DoNothing(p)

Next == \E p \in Procs : Step(p)

SendVote(p) ==
    \/ UponYes(p)
    \/ UponNo(p)

TryDecide(p) ==
    UponSentDecide(p)

Fairness ==
    /\ \A p \in Procs : WF_vars(pc[p] \in {"YES", "NO"} /\ SendVote(p))
    /\ \A p \in Procs : WF_vars(pc[p] = "SENT" /\ TryDecide(p))

Spec == Init /\ [][Next]_vars /\ Fairness

SpecAllYes == InitAllYes /\ [][Next]_vars /\ Fairness

InitialVote(p) ==
    IF pc[p] = "YES" \/ (pc[p] \in {"SENT", "ABORT", "COMMIT", "CRASH"} /\ <<p, "YES">> \in sent)
    THEN "YES"
    ELSE "NO"

AllInitiallyYes ==
    \A p \in Procs : <<p, "YES">> \in sent \/ pc[p] = "YES"

SomeInitiallyNo ==
    \E p \in Procs : <<p, "NO">> \in sent \/ pc[p] = "NO"

Validity ==
    \A p \in Procs :
        pc[p] = "COMMIT" => ~SomeInitiallyNo

Agreement ==
    \A p, q \in Procs :
        (pc[p] = "COMMIT" /\ pc[q] = "ABORT") => FALSE

NoCrash ==
    \A p \in Procs : pc[p] # "CRASH"

Termination ==
    <>(\A p \in Procs : pc[p] \in {"ABORT", "COMMIT", "CRASH"})

=============================================================================