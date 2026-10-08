----------------------------- MODULE FastSlowMutex -----------------------------
EXTENDS Naturals

CONSTANTS N, NoOwner

ASSUME N \in Nat /\ N >= 2 /\ NoOwner \notin 1..N

Proc == 1..N

PCVals == {"Idle", "Intent", "SlowWait", "Retry", "CS"}

VARIABLES pc, intent, owner

vars == << pc, intent, owner >>

ProcState == [Proc -> PCVals]

OwnerSet == Proc \cup {NoOwner}

TypeInv ==
  /\ pc \in ProcState
  /\ intent \in [Proc -> BOOLEAN]
  /\ owner \in OwnerSet

Init ==
  /\ pc = [p \in Proc |-> "Idle"]
  /\ intent = [p \in Proc |-> FALSE]
  /\ owner = NoOwner

NoOtherIntent(p) ==
  \A q \in Proc: q = p \/ intent[q] = FALSE

OthersQuiet(p) == NoOtherIntent(p)

Start(p) ==
  /\ pc[p] = "Idle"
  /\ pc' = [pc EXCEPT ![p] = "Intent"]
  /\ intent' = [intent EXCEPT ![p] = TRUE]
  /\ UNCHANGED owner

TryFastSuccess(p) ==
  /\ pc[p] = "Intent"
  /\ NoOtherIntent(p)
  /\ owner = NoOwner \/ owner = p
  /\ pc' = [pc EXCEPT ![p] = "CS"]
  /\ UNCHANGED intent
  /\ owner' = p

TryFastFail(p) ==
  /\ pc[p] = "Intent"
  /\ ~( NoOtherIntent(p) /\ (owner = NoOwner \/ owner = p) )
  /\ pc' = [pc EXCEPT ![p] = "SlowWait"]
  /\ intent' = [intent EXCEPT ![p] = FALSE]
  /\ UNCHANGED owner

ClaimOwner(p) ==
  /\ pc[p] = "SlowWait"
  /\ owner = NoOwner
  /\ UNCHANGED pc
  /\ UNCHANGED intent
  /\ owner' = p

WaitQuietThenRetry(p) ==
  /\ pc[p] = "SlowWait"
  /\ owner = p
  /\ OthersQuiet(p)
  /\ pc' = [pc EXCEPT ![p] = "Retry"]
  /\ UNCHANGED << intent, owner >>

DoRetry(p) ==
  /\ pc[p] = "Retry"
  /\ pc' = [pc EXCEPT ![p] = "Intent"]
  /\ intent' = [intent EXCEPT ![p] = TRUE]
  /\ UNCHANGED owner

ExitCS(p) ==
  /\ pc[p] = "CS"
  /\ pc' = [pc EXCEPT ![p] = "Idle"]
  /\ intent' = [intent EXCEPT ![p] = FALSE]
  /\ owner' = IF owner = p THEN NoOwner ELSE owner

ProcStep(p) ==
  Start(p)
  \/ TryFastSuccess(p)
  \/ TryFastFail(p)
  \/ ClaimOwner(p)
  \/ WaitQuietThenRetry(p)
  \/ DoRetry(p)
  \/ ExitCS(p)

Next ==
  \E p \in Proc: ProcStep(p)

Spec ==
  Init /\ [][Next]_vars /\ \A p \in Proc: WF_vars(ProcStep(p))

(*
 Safety properties
*)

Mutex ==
  \A p,q \in Proc: p # q => ~(pc[p] = "CS" /\ pc[q] = "CS")

InCSImpliesIntent ==
  \A p \in Proc: pc[p] = "CS" => intent[p] = TRUE

IdleImpliesNoIntent ==
  \A p \in Proc: pc[p] = "Idle" => intent[p] = FALSE

OwnerConsistency ==
  owner = NoOwner \/ (owner \in Proc /\ pc[owner] = "CS")

Safety == TypeInv /\ Mutex /\ InCSImpliesIntent /\ IdleImpliesNoIntent /\ OwnerConsistency

(*
 Liveness properties
*)

GlobalProgress ==
  []<>(\E p \in Proc: pc[p] = "CS")

SlowPathProgress ==
  \A p \in Proc: []( pc[p] = "SlowWait" => <>( pc[p] = "Retry" \/ pc[p] = "CS" ) )

CleanupProgress ==
  \A p \in Proc: []( pc[p] = "CS" => <>( pc[p] = "Idle" /\ intent[p] = FALSE /\ owner = NoOwner ) )

=============================================================================