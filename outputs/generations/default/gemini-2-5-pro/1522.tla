-------------------------------- MODULE Huang --------------------------------
EXTENDS Reals, TLC

CONSTANTS Procs, Leader
ASSUME Leader \in Procs

VARIABLES active, weight, messages, terminated

vars == <<active, weight, messages, terminated>>

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Reals]
    /\ \A p \in Procs: weight[p] >= 0
    /\ messages \subseteq [dest: Procs, w: Reals]
    /\ \A m \in messages: m.w > 0
    /\ terminated \in BOOLEAN

Init ==
    /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
    /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
    /\ messages = {}
    /\ terminated = FALSE

(* An active process p with non-zero weight sends half its weight to process q. *)
Send(p, q) ==
    /\ active[p]
    /\ weight[p] > 0
    /\ LET w_half == weight[p] / 2
       IN /\ weight' = [weight EXCEPT ![p] = w_half]
          /\ messages' = messages \cup {[dest |-> q, w |-> w_half]}
    /\ UNCHANGED <<active, terminated>>

(* A process p receives a message m addressed to it, adding the message's
   weight to its own and becoming active. *)
ReceiveMessage(p) ==
    /\ \E m \in messages: m.dest = p
    /\ LET m == CHOOSE m_ \in messages: m_.dest = p
       IN /\ messages' = messages \setminus {m}
          /\ weight' = [weight EXCEPT ![p] = weight[p] + m.w]
          /\ active' = [active EXCEPT ![p] = TRUE]
    /\ UNCHANGED terminated

(* An active non-leader process p becomes idle, sending its entire weight
   back to the Leader. *)
BecomeIdle(p) ==
    /\ p /= Leader
    /\ active[p]
    /\ messages' = messages \cup {[dest |-> Leader, w |-> weight[p]]}
    /\ weight' = [weight EXCEPT ![p] = 0]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ UNCHANGED terminated

(* The Leader, when its weight is 1, becomes idle and detects termination. *)
DetectTermination ==
    /\ active[Leader]
    /\ weight[Leader] = 1
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ terminated' = TRUE
    /\ UNCHANGED <<weight, messages>>

Next ==
    \/ (\E p, q \in Procs: Send(p, q))
    \/ (\E p \in Procs: ReceiveMessage(p))
    \/ (\E p \in Procs \setminus {Leader}: BecomeIdle(p))
    \/ DetectTermination

(* Fairness: Every process that is able to take a step eventually does. *)
ProcessAction(p) ==
    \/ (\E q \in Procs : Send(p, q))
    \/ ReceiveMessage(p)
    \/ IF p = Leader
       THEN DetectTermination
       ELSE BecomeIdle(p)

Fairness == \A p \in Procs: WF_vars(ProcessAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties of the algorithm *)

(* Helper to sum a set of real numbers. *)
RECURSIVE SumSet(_)
SumSet(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN x + SumSet(S \setminus {x})

(* Safety Invariant: The total weight in the system is always 1. *)
TotalWeightIsOne ==
    SumSet({weight[p] : p \in Procs}) + SumSet({m.w : m \in messages}) = 1

(* Safety Invariant: If termination is detected, all processes are idle
   and no messages are in transit. *)
TerminationSafety ==
    terminated => (\A p \in Procs: ~active[p]) /\ (messages = {})

(* Liveness Property: If the distributed computation eventually quiesces (all
   non-leader processes become permanently idle), then global termination is
   eventually detected. *)
ComputationQuiescent == \A p \in Procs \setminus {Leader}: ~active[p]

TerminationLiveness ==
    (<>[]ComputationQuiescent) ~> <>terminated

THEOREM Spec => []TypeOK
THEOREM Spec => []TotalWeightIsOne
THEOREM Spec => []TerminationSafety
THEOREM Spec => TerminationLiveness

=============================================================================