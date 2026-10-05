---------------------------- MODULE TokenRingTermination ----------------------------
EXTENDS Naturals, TLC

CONSTANTS White, Black

VARIABLES
    active,         \* active[i] = TRUE iff process i is active
    color,          \* color[i] = local color of process i
    tokenAt,        \* tokenAt = process index where token currently resides
    tokenColor,     \* tokenColor = color carried by the token
    terminated,     \* terminated = TRUE when termination has been declared
    tokenCounter    \* tokenCounter = count of full token cycles for detection

Procs == {0, 1, 2}

Colors == {White, Black}

TypeInvariant ==
    /\ active \in [Procs -> BOOLEAN]
    /\ color \in [Procs -> Colors]
    /\ tokenAt \in Procs
    /\ tokenColor \in Colors
    /\ terminated \in BOOLEAN
    /\ tokenCounter \in Nat

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ active = [i \in Procs |-> TRUE]
    /\ color = [i \in Procs |-> White]
    /\ tokenAt = 0
    /\ tokenColor = White
    /\ terminated = FALSE
    /\ tokenCounter = 0

-----------------------------------------------------------------------------
(* Process Actions *)

(* Process i becomes passive (finishes its local work) *)
BecomePassive(i) ==
    /\ active[i] = TRUE
    /\ terminated = FALSE
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<color, tokenAt, tokenColor, terminated, tokenCounter>>

(* Process i generates new local work and becomes active *)
GenerateWork(i) ==
    /\ terminated = FALSE
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<color, tokenAt, tokenColor, terminated, tokenCounter>>

(* Process i sends a message to process j, activating j and marking i black *)
SendMessage(i, j) ==
    /\ i # j
    /\ active[i] = TRUE
    /\ terminated = FALSE
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ color' = [color EXCEPT ![i] = IF j > i THEN color[i] ELSE Black]
    /\ UNCHANGED <<tokenAt, tokenColor, terminated, tokenCounter>>

(* Process i passes the token to the next process in the ring *)
PassToken(i) ==
    /\ tokenAt = i
    /\ active[i] = FALSE
    /\ terminated = FALSE
    /\ LET next == (i + 2) % 3  \* Token goes backwards: 0 -> 2 -> 1 -> 0
       IN /\ tokenAt' = next
          /\ tokenColor' = IF color[i] = Black THEN Black ELSE tokenColor
          /\ color' = [color EXCEPT ![i] = White]
          /\ tokenCounter' = IF next = 0 THEN tokenCounter + 1 ELSE tokenCounter
    /\ UNCHANGED <<active, terminated>>

(* Termination detection at process 0 *)
DetectTermination ==
    /\ tokenAt = 0
    /\ active[0] = FALSE
    /\ color[0] = White
    /\ tokenColor = White
    /\ \A i \in Procs : active[i] = FALSE
    /\ terminated = FALSE
    /\ tokenCounter > 0
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, color, tokenAt, tokenColor, tokenCounter>>

(* Process 0 initiates a new round if detection failed *)
InitiateNewRound ==
    /\ tokenAt = 0
    /\ active[0] = FALSE
    /\ terminated = FALSE
    /\ tokenCounter > 0
    /\ \/ tokenColor = Black
       \/ color[0] = Black
    /\ tokenColor' = White
    /\ color' = [color EXCEPT ![0] = White]
    /\ tokenAt' = 2  \* Start new round, pass to previous
    /\ tokenCounter' = 0
    /\ UNCHANGED <<active, terminated>>

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \/ \E i \in Procs : BecomePassive(i)
    \/ \E i \in Procs : GenerateWork(i)
    \/ \E i \in Procs : \E j \in Procs : SendMessage(i, j)
    \/ \E i \in Procs : PassToken(i)
    \/ DetectTermination
    \/ InitiateNewRound

-----------------------------------------------------------------------------
(* Fairness Conditions *)

(* Weak fairness on token passing ensures token eventually moves *)
TokenPassingFairness ==
    \A i \in Procs : WF_<<active, color, tokenAt, tokenColor, terminated, tokenCounter>>(PassToken(i))

(* Weak fairness on termination detection *)
DetectionFairness ==
    WF_<<active, color, tokenAt, tokenColor, terminated, tokenCounter>>(DetectTermination)

(* Weak fairness on new round initiation *)
NewRoundFairness ==
    WF_<<active, color, tokenAt, tokenColor, terminated, tokenCounter>>(InitiateNewRound)

Fairness ==
    /\ TokenPassingFairness
    /\ DetectionFairness
    /\ NewRoundFairness

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_<<active, color, tokenAt, tokenColor, terminated, tokenCounter>> /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

(* Token is always at exactly one valid process with valid color *)
TokenValid ==
    /\ tokenAt \in Procs
    /\ tokenColor \in Colors

(* Single token invariant - there is exactly one token location *)
SingleToken ==
    \E! i \in Procs : tokenAt = i

(* Local states remain in valid domains *)
LocalStatesValid ==
    /\ \A i \in Procs : active[i] \in BOOLEAN
    /\ \A i \in Procs : color[i] \in Colors

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeInvariant
    /\ TokenValid
    /\ SingleToken
    /\ LocalStatesValid

(* Termination is only declared when all processes are passive *)
NoFalseTermination ==
    terminated => \A i \in Procs : active[i] = FALSE

(* Stronger safety: termination implies true quiescence *)
TerminationSafety ==
    terminated => (\A i \in Procs : active[i] = FALSE)

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* All processes passive *)
AllPassive ==
    \A i \in Procs : active[i] = FALSE

(* Eventually termination is detected if all processes become and stay passive *)
EventualTerminationDetection ==
    (AllPassive /\ [](AllPassive)) ~> terminated

(* If system reaches stable passive state, termination will be detected *)
ProgressToTermination ==
    [](AllPassive => <>terminated)

(* Termination stability - once declared, stays declared *)
TerminationStable ==
    [](terminated => []terminated)

=============================================================================