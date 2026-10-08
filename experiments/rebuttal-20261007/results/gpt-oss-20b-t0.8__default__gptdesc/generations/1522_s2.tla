------------------------------ MODULE HuangTermination ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Procs, Leader
ASSUME Leader \in Procs

VARIABLES active, weight, msgs, terminated

(* Records representing a message in transit *)
Msg == [src:Nat, dst:Nat, w:Real]

vars == <<active, weight, msgs, terminated>>

(* Initial state ---------------------------------------------------------------*)
Init ==
  /\ active = [p \in Procs |-> TRUE]
  /\ weight = [p \in Procs |
                IF p = Leader THEN 1 ELSE 0 ]
  /\ msgs   = {}
  /\ terminated = FALSE

(* Helper functions ------------------------------------------------------------*)
TotalWeight == SUM p \in Procs : weight[p]
TotalMsgWeight == SUM m \in msgs : m.w

Invariant ==
  TotalWeight + TotalMsgWeight = 1
  /\ terminated => (msgs = {} /\ ALL p \in Procs : active[p] = FALSE)

(* Actions ---------------------------------------------------------------------*)

Send(p, q) ==
  /\ p \in Procs
  /\ q \in Procs \ {p}
  /\ active[p] = TRUE
  /\ weight[p] > 0
  /\ ~terminated
  /\ LET half == weight[p]/2 IN
     /\ weight'   = [weight EXCEPT ![p] = weight[p] - half]
     /\ msgs'     = msgs ∪ { [src -> p, dst -> q, w -> half] }
     /\ active'   = active
     /\ terminated'=terminated

Receive(m) ==
  /\ m \in msgs
  /\ ~terminated
  /\ weight'   = [weight EXCEPT ![m.dst] = weight[m.dst] + m.w]
  /\ msgs'     = msgs \ {m}
  /\ active'   = active
  /\ terminated'=terminated

Idle(p) ==
  /\ p \in Procs
  /\ ~terminated
  /\ weight[p] <= 0
  /\ active[p] = TRUE
  /\ active'   = [active EXCEPT ![p] = FALSE]
  /\ weight'   = weight
  /\ msgs'     = msgs
  /\ terminated'=terminated

Terminate ==
  /\ ~terminated
  /\ msgs = {}
  /\ ALL p \in Procs : active[p] = FALSE
  /\ terminated' = TRUE
  /\ active'   = active
  /\ weight'   = weight
  /\ msgs'     = msgs

Next == 
  \E p,q \in Procs : Send(p,q)
  \/ \E m \in msgs : Receive(m)
  \/ \E p \in Procs : Idle(p)
  \/ Terminate

Fairness == WF_(Send) /\ WF_(Receive) /\ WF_(Idle) /\ WF_(Terminate)

Spec == Init /\ []Next /\ Fairness
Safety == []Invariant
Liveness == <> terminated

===============================================================================