----------------------------- MODULE Bakery -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  NumProcs, \* number of processes (>= 1)
  MaxNum    \* maximum ticket value (>= 1)

ASSUME
  /\ NumProcs \in Nat /\ NumProcs >= 1
  /\ MaxNum \in Nat /\ MaxNum >= 1

(*
  Processes are 1..NumProcs. Tickets are in 0..MaxNum with 0 meaning "not contending".
  Each process has:
    - pc[i]     ∈ {"idle","choose1","choose2","wait","cs","exit"} (program counter)
    - choosing[i] ∈ BOOLEAN (announced choosing flag while picking a number)
    - number[i] ∈ 0..MaxNum (ticket; 0 means not contending)
    - j[i] ∈ 1..(NumProcs+1) (current index scanned in waiting protocol; > NumProcs means done)
*)

Proc == 1..NumProcs
TicketVal == 0..MaxNum
PCSet == {"idle","choose1","choose2","wait","cs","exit"}
JRange == 1..(NumProcs + 1)

VARIABLES pc, choosing, number, j

vars == << pc, choosing, number, j >>

Init ==
  /\ pc = [ i \in Proc |-> "idle" ]
  /\ choosing = [ i \in Proc |-> FALSE ]
  /\ number = [ i \in Proc |-> 0 ]
  /\ j = [ i \in Proc |-> 1 ]

(*
  Ordering predicate:
  Before(i,k) means "k has priority over i" according to the Bakery order:
    - k is contending (number[k] # 0)
    - either number[k] < number[i], or same ticket and lower id (k < i)
*)
Before(i, k) ==
  /\ k \in Proc /\ i \in Proc
  /\ number[k] # 0
  /\ ( number[k] < number[i] \/ (number[k] = number[i] /\ k < i) )

(*
  Enabledness predicates (state-only) for deadlock inspection
*)
StartChooseEn(i) == pc[i] = "idle"
PickNumberEn(i)  == pc[i] = "choose1"
FinishChooseEn(i)== pc[i] = "choose2"
WaitAdvanceEn(i) ==
  /\ pc[i] = "wait" /\ j[i] <= NumProcs
  /\ ( j[i] = i \/ ( ~choosing[j[i]] /\ ~Before(i, j[i]) ) )
EnterCSEn(i)     == /\ pc[i] = "wait" /\ j[i] > NumProcs
ExitCSEn(i)      == pc[i] = "cs"
ReleaseEn(i)     == pc[i] = "exit"

StepExists ==
  \E i \in Proc:
       StartChooseEn(i) \/ PickNumberEn(i) \/ FinishChooseEn(i)
    \/ WaitAdvanceEn(i) \/ EnterCSEn(i)    \/ ExitCSEn(i)     \/ ReleaseEn(i)

(*
  Process actions
*)
StartChoose(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "choose1"]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED << number, j >>

PickNumber(i) ==
  /\ i \in Proc
  /\ pc[i] = "choose1"
  /\ LET maxN == Max({ number[k] : k \in Proc })
         n    == IF maxN + 1 <= MaxNum THEN maxN + 1 ELSE MaxNum
     IN /\ number' = [number EXCEPT ![i] = n]
        /\ pc' = [pc EXCEPT ![i] = "choose2"]
        /\ UNCHANGED << choosing, j >>

FinishChoose(i) ==
  /\ i \in Proc
  /\ pc[i] = "choose2"
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED number

WaitAdvance(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ j[i] <= NumProcs
  /\ ( j[i] = i \/ ( ~choosing[j[i]] /\ ~Before(i, j[i]) ) )
  /\ j' = [j EXCEPT ![i] = @ + 1]
  /\ UNCHANGED << pc, choosing, number >>

EnterCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ j[i] > NumProcs
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << choosing, number, j >>

ExitCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << choosing, number, j >>

Release(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ number' = [number EXCEPT ![i] = 0]
  /\ UNCHANGED << choosing, j >>

Next ==
  \E i \in Proc:
       StartChoose(i) \/ PickNumber(i) \/ FinishChoose(i)
    \/ WaitAdvance(i) \/ EnterCS(i)    \/ ExitCS(i)     \/ Release(i)

(*
  Fairness assumptions (weak fairness) on the protocol steps after a process starts trying.
  These ensure that if any of these actions is continuously enabled for a process,
  it will eventually occur, ruling out starvation assuming others make progress.
*)
Fairness ==
  \A i \in Proc:
       WF_vars(PickNumber(i))
    /\ WF_vars(FinishChoose(i))
    /\ WF_vars(WaitAdvance(i))
    /\ WF_vars(EnterCS(i))
    /\ WF_vars(ExitCS(i))
    /\ WF_vars(Release(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(*
  Safety and structural invariants
*)
TypeInv ==
  /\ pc \in [Proc -> PCSet]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> TicketVal]
  /\ j \in [Proc -> JRange]

TicketBoundInv == \A i \in Proc: number[i] \in TicketVal

MutualExclusion ==
  Cardinality({ i \in Proc : pc[i] = "cs" }) <= 1

ChoosingPhaseInv ==
  \A i \in Proc: choosing[i] => pc[i] \in {"choose1","choose2"}

TicketPhaseInv ==
  /\ \A i \in Proc: pc[i] \in {"wait","cs","exit"} => number[i] # 0
  /\ \A i \in Proc: pc[i] = "idle" => number[i] = 0

TotalOrderInv ==
  \A i, k \in Proc:
    i # k /\ number[i] # 0 /\ number[k] # 0
      => (Before(i,k) # Before(k,i))  \* exactly one holds

CSDominanceInv ==
  \A i \in Proc:
    pc[i] = "cs" => \A k \in Proc \ {i}: ~Before(i,k)

NoDeadlockState == StepExists

Invariant ==
  /\ TypeInv
  /\ TicketBoundInv
  /\ MutualExclusion
  /\ ChoosingPhaseInv
  /\ TicketPhaseInv
  /\ TotalOrderInv
  /\ CSDominanceInv
  /\ NoDeadlockState

(*
  Additional temporal properties (for model checking if desired):

  - Starvation-freedom under the given fairness: a process that is trying
    (in choose/wait phases) will eventually enter CS.
*)
TryState(i) == pc[i] \in {"choose1","choose2","wait"}

StarvationFreedom ==
  \A i \in Proc: []( TryState(i) => <> (pc[i] = "cs") )

(*
  - Eventual reset: after exiting the CS, the process eventually resets its ticket.
*)
ResetEventually ==
  \A i \in Proc: []( pc[i] = "exit" => <> (pc[i] = "idle" /\ number[i] = 0) )

(*
  - Ticket bound safety as a temporal property (redundant with TicketBoundInv inside Invariant).
*)
TicketBound ==
  []( \A i \in Proc: number[i] \in TicketVal )

=============================================================================