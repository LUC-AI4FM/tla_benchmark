--------------------------- MODULE Huang ----------------------------
EXTENDS Naturals, Reals, Sequences

CONSTANTS Procs, Leader
ASSUME Leader \in Procs

VARIABLES active, weight, queue, terminated

Vars == <<active, weight, queue, terminated>>

Init ==
   /\ active = [p \in Procs |-> TRUE]
   /\ weight = [Leader |-> 1] \u [p \in Procs \ {Leader} |-> 0]
   /\ queue = [p \in Procs |-> <>]
   /\ terminated = FALSE

Send(p,q) ==
   /\ p \in Procs
   /\ q \in Procs
   /\ p # q
   /\ active[p] = TRUE
   /\ weight[p] > 0
   /\ LET m == weight[p]/2 IN
        /\ active'   = [active EXCEPT ![p] = FALSE]
        /\ weight'   = [weight EXCEPT ![p] = m]
        /\ queue'    = [queue EXCEPT ![q] = Append(queue[q], m)]
        /\ terminated' = terminated

Receive(q) ==
   /\ q \in Procs
   /\ queue[q] # <> 
   /\ LET m == Head(queue[q]) IN
        /\ active'   = [active EXCEPT ![q] = FALSE]
        /\ weight'   = [weight EXCEPT ![q] = weight[q] + m]
        /\ queue'    = [queue EXCEPT ![q] = Tail(queue[q])]
        /\ terminated' = terminated

DetectTerm ==
   /\ terminated = FALSE
   /\ \A p \in Procs : (active[p] = FALSE) /\ (queue[p] = <>)
   /\ terminated' = TRUE
   /\ UNCHANGED << active, weight, queue >>

Next ==
   \/ \E p \in Procs, q \in Procs : Send(p,q)
   \/ \E q \in Procs : Receive(q)
   \/ DetectTerm

TotalWeight ==
  \Sum_{p \in Procs} weight[p] + \Sum_{p \in Procs} \Sum(queue[p])

Invariant_TotalWeightIsOne == TotalWeight = 1
Invariant_TerminationSafety == terminated /\ (\A p \in Procs : (active[p] = FALSE) /\ (queue[p] = <>))

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next) /\ Invariant_TotalWeightIsOne /\ Invariant_TerminationSafety

TerminationLiveness == []<> terminated
=============================================================================