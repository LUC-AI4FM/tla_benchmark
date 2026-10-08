------------------------------- MODULE NBACProtocol -------------------------------

CONSTANTS N \* Number of processes

VARIABLES pc, sent, rcvd, fd

\* Process states
PC_STATES == {"YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH"}

Init ==
  /\ pc = [p \in 1..N -> CHOOSE v \in {"YES", "NO"}]
  /\ sent = {}
  /\ rcvd = [p \in 1..N -> {}]
  /\ fd = FALSE

InitAllYes ==
  /\ pc = [p \in 1..N -> "YES"]
  /\ sent = {}
  /\ rcvd = [p \in 1..N -> {}]
  /\ fd = FALSE

\* Actions
UponYes(p) ==
  /\ pc[p] = "YES"
  /\ fd = FALSE
  /\ sent' = sent \cup {<<p, "YES">>}
  /\ rcvd' = rcvd
  /\ pc' = [pc EXCEPT ![p] = "SENT"]
  /\ UNCHANGED <<fd>>

UponNo(p) ==
  /\ pc[p] = "NO"
  /\ fd = FALSE
  /\ sent' = sent \cup {<<p, "NO">>}
  /\ rcvd' = rcvd
  /\ pc' = [pc EXCEPT ![p] = "SENT"]
  /\ UNCHANGED <<fd>>

UponSent(p) ==
  /\ pc[p] = "SENT"
  /\ fd = FALSE
  /\ \A q \in 1..N : (q \notin DOMAIN sent => rcvd[q] = {})
  /\ (\E m \in sent: snd(m) = "NO") \/ (\E q \in 1..N : q \notin {p' \in 1..N : <<p', "YES">> \in sent})
    -> (pc' = [pc EXCEPT ![p] = "ABORT"] /\ UNCHANGED <<sent, rcvd>>)
  /\ (\A m \in sent: snd(m) = "YES") /\ (\A q \in 1..N : <<q, "YES">> \in sent)
    -> (pc' = [pc EXCEPT ![p] = "COMMIT"] /\ UNCHANGED <<sent, rcvd>>)

UponCrash(p) ==
  /\ pc[p] \notin {"ABORT", "COMMIT"}
  /\ fd = FALSE
  /\ pc' = [pc EXCEPT ![p] = "CRASH"]
  /\ UNCHANGED <<sent, rcvd>>

Next ==
  \/ \E p \in 1..N : UponYes(p)
  \/ \E p \in 1..N : UponNo(p)
  \/ \E p \in 1..N : UponSent(p)
  \/ \E p \in 1..N : UponCrash(p)

\* Weak fairness
WF ==
  WF_vars(<<pc, sent>>, {p \in 1..N : pc[p] \notin {"ABORT", "COMMIT", "CRASH"}}, Next)

Spec ==
  Init \/ InitAllYes
  /\ [][Next]_<<pc, sent, rcvd, fd>>
  /\ WF

\* Type invariants
TypeOK ==
  /\ pc \in [1..N -> PC_STATES]
  /\ sent \subseteq (1..N) \X {"YES", "NO"}
  /\ rcvd \in [1..N -> SUBSET (1..N) \X {"YES", "NO"}]
  /\ fd \in BOOLEAN

\* Validity property
Validity ==
  \/ (\E p \in 1..N : pc[p] = "COMMIT") -> (\A q \in 1..N : pc[q] = "YES")

=============================================================================