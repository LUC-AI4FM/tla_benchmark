------------------------------ MODULE TerminationRing3 ------------------------------

EXTENDS Naturals

CONSTANT Proc

ASSUME Proc = 0..2

(*
  Ring successor
*)
NextProc(i) == IF i = 2 THEN 0 ELSE i + 1

(*
  Colors are booleans: FALSE = white, TRUE = black
*)

VARIABLES
  active,         \* [Proc -> BOOLEAN], whether process has outstanding work
  localColor,     \* [Proc -> BOOLEAN], per-process color bit
  work,           \* [Proc -> Nat], local pending work units
  tokenAt,        \* element of Proc, current token holder
  tokenColor,     \* BOOLEAN, token color bit
  genEnabled,     \* [Proc -> BOOLEAN], whether process may still generate new work
  detectorDeclared \* BOOLEAN, whether termination has been declared

vars == << active, localColor, work, tokenAt, tokenColor, genEnabled, detectorDeclared >>

(*
  Helper predicates
*)
AllPassive == \A i \in Proc: active[i] = FALSE
NoWork     == \A i \in Proc: work[i] = 0
NoPotential == \A i \in Proc: genEnabled[i] = FALSE
AllWhite   == \A i \in Proc: localColor[i] = FALSE

SetActiveFromWork(w) == [i \in Proc |-> w[i] > 0]

(*
  Initial states: arbitrary within types; a single token located at some process; detector not yet declared
*)
Init ==
  /\ work \in [Proc -> Nat]
  /\ active = SetActiveFromWork(work)
  /\ localColor \in [Proc -> BOOLEAN]
  /\ tokenAt \in Proc
  /\ tokenColor \in BOOLEAN
  /\ genEnabled \in [Proc -> BOOLEAN]
  /\ detectorDeclared = FALSE

(*
  Actions
*)

Generate(i) ==
  /\ i \in Proc
  /\ ~detectorDeclared
  /\ genEnabled[i]
  /\ LET w2 == [work EXCEPT ![i] = work[i] + 1] IN
     /\ work' = w2
     /\ active' = SetActiveFromWork(work')
  /\ localColor' = [localColor EXCEPT ![i] = TRUE]
  /\ UNCHANGED << tokenAt, tokenColor, genEnabled, detectorDeclared >>

DoWork(i) ==
  /\ i \in Proc
  /\ ~detectorDeclared
  /\ work[i] > 0
  /\ LET w2 == [work EXCEPT ![i] = work[i] - 1] IN
     /\ work' = w2
     /\ active' = SetActiveFromWork(work')
  /\ UNCHANGED << localColor, tokenAt, tokenColor, genEnabled, detectorDeclared >>

DisableGen(i) ==
  /\ i \in Proc
  /\ ~detectorDeclared
  /\ genEnabled[i]
  /\ genEnabled' = [genEnabled EXCEPT ![i] = FALSE]
  /\ UNCHANGED << active, localColor, work, tokenAt, tokenColor, detectorDeclared >>

(*
  Non-root token pass: accumulate blackness, reset local color
*)
PassNonRoot(i) ==
  /\ i \in (Proc \ {0})
  /\ ~detectorDeclared
  /\ tokenAt = i
  /\ tokenAt' = NextProc(i)
  /\ tokenColor' = tokenColor \/ localColor[i]
  /\ localColor' = [localColor EXCEPT ![i] = FALSE]
  /\ UNCHANGED << active, work, genEnabled, detectorDeclared >>

(*
  Root behavior: either declare termination (when safe) or forward a fresh white token
*)
RootCanDeclare ==
  /\ tokenAt = 0
  /\ tokenColor = FALSE
  /\ AllPassive
  /\ NoWork
  /\ NoPotential

DeclareTermination ==
  /\ ~detectorDeclared
  /\ RootCanDeclare
  /\ detectorDeclared' = TRUE
  /\ UNCHANGED << active, localColor, work, tokenAt, tokenColor, genEnabled >>

(*
  Root forwards token for next cycle: reset token to white (outgoing color = localColor[0]), reset localColor[0]
*)
RootForward ==
  /\ ~detectorDeclared
  /\ tokenAt = 0
  /\ ~RootCanDeclare
  /\ tokenAt' = NextProc(0)
  /\ tokenColor' = localColor[0]
  /\ localColor' = [localColor EXCEPT ![0] = FALSE]
  /\ UNCHANGED << active, work, genEnabled, detectorDeclared >>

Next ==
  \/ (\E i \in Proc: Generate(i))
  \/ (\E i \in Proc: DoWork(i))
  \/ (\E i \in Proc: DisableGen(i))
  \/ (\E i \in (Proc \ {0}): PassNonRoot(i))
  \/ RootForward
  \/ DeclareTermination

Spec ==
  Init /\ [][Next]_vars
  /\ \A i \in (Proc \ {0}): WF_vars(PassNonRoot(i))
  /\ WF_vars(RootForward)
  /\ \A i \in Proc: WF_vars(DoWork(i))

(*
  Safety properties
*)
TokenSafety ==
  /\ tokenAt \in Proc
  /\ tokenColor \in BOOLEAN

NoTwoTokens ==
  tokenAt \in Proc

LocalStateSafety ==
  /\ active \in [Proc -> BOOLEAN]
  /\ localColor \in [Proc -> BOOLEAN]
  /\ work \in [Proc -> Nat]
  /\ genEnabled \in [Proc -> BOOLEAN]
  /\ detectorDeclared \in BOOLEAN

ActivityMatchesWork ==
  \A i \in Proc: active[i] <=> work[i] > 0

NoPrematureDetection ==
  detectorDeclared => /\ AllPassive /\ NoWork /\ NoPotential /\ tokenAt = 0 /\ tokenColor = FALSE

SafetyInvariants ==
  /\ TokenSafety
  /\ NoTwoTokens
  /\ LocalStateSafety
  /\ ActivityMatchesWork
  /\ NoPrematureDetection

(*
  Liveness and correctness properties for termination detection
*)
EventualTermination ==
  (<>[] (AllPassive /\ NoWork /\ NoPotential)) => (<> detectorDeclared)

NoFalsePositives ==
  [] (detectorDeclared => AllPassive /\ NoWork /\ NoPotential)

WhiteTokenEventuallyAtRootUnderQuiescence ==
  (<>[] (AllPassive /\ NoWork /\ NoPotential)) => (<> (tokenAt = 0 /\ tokenColor = FALSE))

=============================================================================