---- MODULE NBAC ----
EXTENDS Naturals

(*
  Non-Blocking Atomic Commitment (NBAC) with crash failures.
  Processes start with a vote YES or NO and must decide COMMIT or ABORT.
  Each step, a chosen non-crashed process may:
    - receive some of the already sent messages,
    - update its local failure-detector flag,
    - then either broadcast its vote, decide, crash, or do nothing.
  A process commits only if it suspects no crashes and has received YES from all processes.
*)

CONSTANT N

Proc == 1..N

MsgType == {"YES", "NO"}

PcStates == {"YES", "NO", "SENT", "ABORT", "COMMIT", "CRASH"}

Msg == [from: Proc, type: MsgType]

YesMsgFrom(p) == [from |-> p, type |-> "YES"]
NoMsgFrom(p)  == [from |-> p, type |-> "NO"]

VARIABLES pc, sent, rcvd, fd, ivote

vars == << pc, sent, rcvd, fd, ivote >>

AllYes(R) == \A q \in Proc: YesMsgFrom(q) \in R

Alive(p) == pc[p] \in {"YES", "NO", "SENT"}

Init ==
  /\ pc \in [Proc -> MsgType]
  /\ ivote = pc
  /\ sent = {}
  /\ rcvd = [p \in Proc |-> {}]
  /\ fd \in [Proc -> BOOLEAN]

(*
  Alternate initial condition where everyone votes YES.
*)
InitAllYes ==
  /\ pc = [p \in Proc |-> "YES"]
  /\ ivote = pc
  /\ sent = {}
  /\ rcvd = [p \in Proc |-> {}]
  /\ fd \in [Proc -> BOOLEAN]

Broadcast(p) ==
  /\ Alive(p)
  /\ pc[p] \in {"YES", "NO"}
  /\ \E r \in SUBSET sent, f \in BOOLEAN:
       /\ rcvd[p] \subseteq r
       /\ pc'   = [pc EXCEPT ![p] = "SENT"]
       /\ sent' = sent \cup { [from |-> p, type |-> pc[p]] }
       /\ rcvd' = [rcvd EXCEPT ![p] = r]
       /\ fd'   = [fd EXCEPT ![p] = f]
       /\ ivote' = ivote

Decide(p) ==
  /\ Alive(p)
  /\ pc[p] = "SENT"
  /\ \E r \in SUBSET sent, f \in BOOLEAN:
       /\ rcvd[p] \subseteq r
       /\ pc' =
            [pc EXCEPT
               ![p] = IF (~f) /\ AllYes(r) THEN "COMMIT" ELSE "ABORT"]
       /\ UNCHANGED sent
       /\ rcvd' = [rcvd EXCEPT ![p] = r]
       /\ fd'   = [fd EXCEPT ![p] = f]
       /\ ivote' = ivote

Crash(p) ==
  /\ Alive(p)
  /\ \E r \in SUBSET sent, f \in BOOLEAN:
       /\ rcvd[p] \subseteq r
       /\ pc'   = [pc EXCEPT ![p] = "CRASH"]
       /\ UNCHANGED sent
       /\ rcvd' = [rcvd EXCEPT ![p] = r]
       /\ fd'   = [fd EXCEPT ![p] = f]
       /\ ivote' = ivote

DoNothing(p) ==
  /\ Alive(p)
  /\ \E r \in SUBSET sent, f \in BOOLEAN:
       /\ rcvd[p] \subseteq r
       /\ UNCHANGED << pc, sent >>
       /\ rcvd' = [rcvd EXCEPT ![p] = r]
       /\ fd'   = [fd EXCEPT ![p] = f]
       /\ ivote' = ivote

Next ==
  \E p \in Proc:
    Broadcast(p) \/ Decide(p) \/ Crash(p) \/ DoNothing(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A p \in Proc: WF_vars(Broadcast(p)))
  /\ (\A p \in Proc: WF_vars(Decide(p)))

TypeOK ==
  /\ pc \in [Proc -> PcStates]
  /\ ivote \in [Proc -> MsgType]
  /\ sent \subseteq Msg
  /\ rcvd \in [Proc -> SUBSET Msg]
  /\ \A p \in Proc: rcvd[p] \subseteq sent
  /\ fd \in [Proc -> BOOLEAN]

Committed == \E p \in Proc: pc[p] = "COMMIT"
AllInitYes == \A p \in Proc: ivote[p] = "YES"

(*
  Validity: a commit decision can occur only if all initial votes were YES.
*)
Validity == [](Committed => AllInitYes)

====