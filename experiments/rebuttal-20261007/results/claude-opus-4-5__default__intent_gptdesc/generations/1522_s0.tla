---------------------------- MODULE HuangTermination ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, Reals, TLC

CONSTANTS 
    Procs,          \* Set of all processes
    Leader,         \* The designated coordinator process
    MaxDenom        \* Maximum denominator to prevent Zeno behavior

ASSUME Leader \in Procs
ASSUME MaxDenom \in Nat /\ MaxDenom > 0

VARIABLES
    active,         \* active[p] = TRUE iff process p is active
    weight,         \* weight[p] = <<num, denom>> representing num/denom for process p
    messages,       \* Set of messages in transit, each <<sender, receiver, <<num, denom>>>>
    terminated      \* TRUE iff leader has detected termination

vars == <<active, weight, messages, terminated>>

--------------------------------------------------------------------------------
\* Weight arithmetic using rational numbers represented as <<numerator, denominator>>
\* We keep weights as pairs <<n, d>> meaning n/d where d is a power of 2

\* Add two weights: a/b + c/d = (a*d + c*b) / (b*d)
WeightAdd(w1, w2) ==
    LET n1 == w1[1] n2 == w2[1]
        d1 == w1[2] d2 == w2[2]
        newNum == n1 * d2 + n2 * d1
        newDenom == d1 * d2
    IN <<newNum, newDenom>>

\* Check if weight is zero
IsZeroWeight(w) == w[1] = 0

\* Check if weight equals 1 (full weight)
IsFullWeight(w) == w[1] = w[2] /\ w[2] > 0

\* Check if weight is positive
IsPositiveWeight(w) == w[1] > 0 /\ w[2] > 0

\* Split weight in half: (n/d) / 2 = n / (2*d)
HalfWeight(w) == <<w[1], w[2] * 2>>

\* Zero weight
ZeroWeight == <<0, 1>>

\* Full weight (equals 1)
FullWeight == <<1, 1>>

\* Check if denominator is within bounds
ValidDenom(w) == w[2] <= MaxDenom

--------------------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ \A p \in Procs: weight[p][1] \in Nat /\ weight[p][2] \in Nat \ {0}
    /\ \A m \in messages: m[1] \in Procs /\ m[2] \in Procs 
                          /\ m[3][1] \in Nat /\ m[3][2] \in Nat \ {0}
    /\ terminated \in BOOLEAN

--------------------------------------------------------------------------------
\* Initial state: Leader is active with weight 1, others idle with weight 0
Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN FullWeight ELSE ZeroWeight]
    /\ messages = {}
    /\ terminated = FALSE

--------------------------------------------------------------------------------
\* Sum of all weights in the system
SumWeights(ws) ==
    LET AddPair(acc, w) == WeightAdd(acc, w)
    IN  LET RECURSIVE SumSet(_)
            SumSet(S) == IF S = {} THEN ZeroWeight
                         ELSE LET x == CHOOSE x \in S: TRUE
                              IN WeightAdd(x, SumSet(S \ {x}))
        IN SumSet(ws)

AllLocalWeights == {weight[p] : p \in Procs}
AllMessageWeights == {m[3] : m \in messages}
AllWeights == AllLocalWeights \cup AllMessageWeights

TotalWeight == SumWeights(AllWeights)

--------------------------------------------------------------------------------
\* Actions

\* An active process p sends a message with half its weight to process q
\* Process p keeps the other half
SendMessage(p, q) ==
    /\ active[p]
    /\ ~terminated
    /\ IsPositiveWeight(weight[p])
    /\ ValidDenom(HalfWeight(weight[p]))  \* State constraint on denominator
    /\ p # q
    /\ LET halfW == HalfWeight(weight[p])
       IN /\ weight' = [weight EXCEPT ![p] = halfW]
          /\ messages' = messages \cup {<<p, q, halfW>>}
    /\ UNCHANGED <<active, terminated>>

\* An idle process q receives a message and becomes active
ReceiveAndActivate(q) ==
    /\ ~active[q]
    /\ ~terminated
    /\ \E m \in messages:
        /\ m[2] = q
        /\ weight' = [weight EXCEPT ![q] = WeightAdd(weight[q], m[3])]
        /\ messages' = messages \ {m}
        /\ active' = [active EXCEPT ![q] = TRUE]
    /\ UNCHANGED <<terminated>>

\* An active process q receives a message (stays active, adds weight)
ReceiveWhileActive(q) ==
    /\ active[q]
    /\ ~terminated
    /\ \E m \in messages:
        /\ m[2] = q
        /\ weight' = [weight EXCEPT ![q] = WeightAdd(weight[q], m[3])]
        /\ messages' = messages \ {m}
    /\ UNCHANGED <<active, terminated>>

\* A non-leader active process becomes idle and sends its weight to the leader
BecomeIdle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ ~terminated
    /\ IsPositiveWeight(weight[p])
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ messages' = messages \cup {<<p, Leader, weight[p]>>}
    /\ weight' = [weight EXCEPT ![p] = ZeroWeight]
    /\ UNCHANGED <<terminated>>

\* Leader becomes idle: sends weight to itself (effectively keeps it, waits for accumulation)
LeaderBecomeIdle ==
    /\ active[Leader]
    /\ ~terminated
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, messages, terminated>>

\* Leader detects termination when idle and has accumulated full weight
DetectTermination ==
    /\ ~active[Leader]
    /\ ~terminated
    /\ IsFullWeight(weight[Leader])
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, weight, messages>>

--------------------------------------------------------------------------------
\* Next state relation
Next ==
    \/ \E p, q \in Procs: SendMessage(p, q)
    \/ \E q \in Procs: ReceiveAndActivate(q)
    \/ \E q \in Procs: ReceiveWhileActive(q)
    \/ \E p \in Procs: BecomeIdle(p)
    \/ LeaderBecomeIdle
    \/ DetectTermination

--------------------------------------------------------------------------------
\* Fairness conditions for liveness
\* Weak fairness on receiving messages ensures messages are eventually delivered
\* Weak fairness on detection ensures leader eventually detects when possible

Fairness ==
    /\ \A q \in Procs: WF_vars(ReceiveAndActivate(q))
    /\ \A q \in Procs: WF_vars(ReceiveWhileActive(q))
    /\ WF_vars(DetectTermination)

--------------------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* Safety Properties

\* Weight conservation: total weight always equals 1
\* Expressed as: sum of all numerator/denominator ratios equals 1
WeightConservation ==
    LET localSum == SumWeights({weight[p] : p \in Procs})
        msgSum == SumWeights({m[3] : m \in messages})
        total == WeightAdd(localSum, msgSum)
    IN IsFullWeight(total)

\* Once terminated, all processes are idle and no messages in transit
TerminationSafety ==
    terminated => 
        /\ \A p \in Procs: ~active[p]
        /\ messages = {}

\* Stability: once terminated, system stays terminated
TerminationStable ==
    [][terminated => terminated']_vars

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ WeightConservation
    /\ TerminationSafety

--------------------------------------------------------------------------------
\* Liveness Properties

\* Global quiescence: all processes idle and no messages
GlobalQuiescence ==
    /\ \A p \in Procs: ~active[p]
    /\ messages = {}

\* Liveness: if global quiescence occurs, eventually termination is detected
TerminationDetection ==
    GlobalQuiescence ~> terminated

--------------------------------------------------------------------------------
\* State constraint to prevent infinite state space (for model checking)
StateConstraint ==
    /\ \A p \in Procs: weight[p][2] <= MaxDenom
    /\ \A m \in messages: m[3][2] <= MaxDenom
    /\ Cardinality(messages) <= Cardinality(Procs) * Cardinality(Procs)

================================================================================