------------------------------- MODULE MutualExclusionLock -------------------------------

CONSTANTS
    \* The set of processes
    Procs == {1, 2}

VARIABLES
    \* The current location of each process (either "nc" for non-critical, "l1" for waiting, or "cs" for critical section)
    loc,
    \* Boolean variable indicating whether the lock is held
    lock

(*--algorithm mutual_exclusion_lock
variables loc = [p \in Procs |-> "nc"], lock = FALSE;

process (P \in Procs)
begin
NonCritical:
  while TRUE do
    await loc[P] = "nc";
    loc[P] := "l1";
Waiting:
    if P = 1 then
      await \neg lock;
      lock := TRUE;
    else
      await \neg lock;
      lock := TRUE;
    end if;
    loc[P] := "cs";
CriticalSection:
    await loc[P] = "cs";
    loc[P] := "nc";
    lock := FALSE;
  end while;
end process;

end algorithm *)

\* TLA+ translation of the PlusCal algorithm
Spec ==
  /\ TYPEOK
  /\ LockInv
  /\ Init
  /\ [][Next]_<<loc, lock>>

Init ==
  /\ loc = [p \in Procs |-> "nc"]
  /\ lock = FALSE

Next ==
  \/ \E p \in Procs : NonCriticalAction(p)
  \/ \E p \in Procs : WaitingAction(p)
  \/ \E p \in Procs : CriticalSectionAction(p)

NonCriticalAction(p) ==
  /\ loc[p] = "nc"
  /\ loc' = [loc EXCEPT ![p] = "l1"]
  /\ lock' = lock

WaitingAction(p) ==
  /\ loc[p] = "l1"
  /\ \neg lock
  /\ loc' = [loc EXCEPT ![p] = "cs"]
  /\ lock' = TRUE

CriticalSectionAction(p) ==
  /\ loc[p] = "cs"
  /\ loc' = [loc EXCEPT ![p] = "nc"]
  /\ lock' = FALSE

\* Type correctness
TypeOK ==
  /\ loc \in [Procs -> {"nc", "l1", "cs"}]
  /\ lock \in BOOLEAN

\* Mutual exclusion invariant
LockInv ==
  \/ \neg lock
  \/ (\E p \in Procs : loc[p] = "cs" /\ \A q \in Procs \ {p} : loc[q] \notin {"cs"})

\* Liveness property: If process 1 is at location "l1", it will eventually reach the critical section
Liveness ==
  <>[](loc[1] = "l1") -> <>(loc[1] = "cs")

=============================================================================