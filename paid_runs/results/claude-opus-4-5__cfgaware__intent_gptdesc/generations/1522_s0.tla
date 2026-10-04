---------------------------- MODULE HuangTermination ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, Reals, TLC

CONSTANTS
    Procs,          \* The set of all processes
    Leader,         \* The designated coordinator process
    MaxDenom        \* Maximum denominator to bound weight fractions

ASSUME Leader \in Procs
ASSUME MaxDenom \in Nat /\ MaxDenom > 0

VARIABLES
    active,         \* active[p] = TRUE iff process p is active
    weight,         \* weight[p] = local weight held by process p (as <<num, denom>>)
    messages,       \* Set of messages in transit, each message is <<dest, <<num, denom>>>>
    terminated      \* TRUE iff leader has detected termination

vars == <<active, weight, messages, terminated>>

\* Weight is represented as a pair <<numerator, denominator>> to avoid real arithmetic
\* Weight <<n, d>> represents the fraction n/d

\* Helper: Add two weights represented as <<num, denom>>
AddWeight(w1, w2) ==
    LET n1 == w1[1] n2 == w2[1]
        d1 == w1[2] d2 == w2[2]
        newNum == n1 * d2 + n2 * d1
        newDenom == d1 * d2
    IN <<newNum, newDenom>>

\* Helper: Check if weight equals zero
IsZeroWeight(w) == w[1] = 0

\* Helper: Check if weight equals 1 (num = denom)
IsOneWeight(w) == w[1] = w[2] /\ w[1] > 0

\* Helper: Split a weight in half
HalfWeight(w) == <<w[1], w[2] * 2>>

\* Helper: Check if a weight is valid (denominator within bounds)
ValidWeight(w) == w[2] <= MaxDenom /\ w[2] > 0 /\ w[1] >= 0

\* Sum of all local weights
SumLocalWeights ==
    LET RECURSIVE SumOver(_)
        SumOver(S) == IF S = {} THEN <<0, 1>>
                      ELSE LET p == CHOOSE x \in S : TRUE
                           IN AddWeight(weight[p], SumOver(S \ {p}))
    IN SumOver(Procs)

\* Sum of all message weights
SumMessageWeights ==
    LET RECURSIVE SumOverMsgs(_)
        SumOverMsgs(S) == IF S = {} THEN <<0, 1>>
                          ELSE LET m == CHOOSE x \in S : TRUE
                               IN AddWeight(m[2], SumOverMsgs(S \ {m}))
    IN SumOverMsgs(messages)

\* Total weight in the system
TotalWeight == AddWeight(SumLocalWeights, SumMessageWeights)

\* Initial state: Leader is active with weight 1, others are idle with weight 0
Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN <<1, 1>> ELSE <<0, 1>>]
    /\ messages = {}
    /\ terminated = FALSE

\* An active process p activates another process q by sending half its weight
\* Process p must have positive weight that can be split within bounds
Activate(p, q) ==
    /\ p /= q
    /\ active[p]
    /\ ~active[q]
    /\ ~IsZeroWeight(weight[p])
    /\ ValidWeight(HalfWeight(weight[p]))  \* State constraint on weight splitting
    /\ weight' = [weight EXCEPT ![p] = HalfWeight(weight[p])]
    /\ messages' = messages \cup {<<q, HalfWeight(weight[p])>>}
    /\ active' = active
    /\ terminated' = terminated

\* An active process p sends a weight-carrying message to process q
\* without necessarily activating q (q might already be active)
SendWeight(p, q) ==
    /\ p /= q
    /\ active[p]
    /\ ~IsZeroWeight(weight[p])
    /\ ValidWeight(HalfWeight(weight[p]))
    /\ weight' = [weight EXCEPT ![p] = HalfWeight(weight[p])]
    /\ messages' = messages \cup {<<q, HalfWeight(weight[p])>>}
    /\ active' = active
    /\ terminated' = terminated

\* Process p receives a message carrying weight
Receive(p, msg) ==
    /\ msg \in messages
    /\ msg[1] = p
    /\ ValidWeight(AddWeight(weight[p], msg[2]))
    /\ weight' = [weight EXCEPT ![p] = AddWeight(weight[p], msg[2])]
    /\ messages' = messages \ {msg}
    /\ active' = [active EXCEPT ![p] = TRUE]  \* Receiving a message activates the process
    /\ terminated' = terminated

\* Non-leader process p becomes idle and sends its weight to the leader
BecomeIdle(p) ==
    /\ p /= Leader
    /\ active[p]
    /\ ~IsZeroWeight(weight[p])
    /\ messages' = messages \cup {<<Leader, weight[p]>>}
    /\ weight' = [weight EXCEPT ![p] = <<0, 1>>]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ terminated' = terminated

\* Non-leader process p becomes idle when it has zero weight (just stops being active)
BecomeIdleZeroWeight(p) ==
    /\ p /= Leader
    /\ active[p]
    /\ IsZeroWeight(weight[p])
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<weight, messages, terminated>>

\* Leader becomes idle and sends weight to itself (accumulates internally)
LeaderBecomeIdle ==
    /\ active[Leader]
    /\ ~IsOneWeight(weight[Leader])  \* Leader doesn't become idle if it has all weight
    /\ ~IsZeroWeight(weight[Leader])
    /\ messages' = messages \cup {<<Leader, weight[Leader]>>}
    /\ weight' = [weight EXCEPT ![Leader] = <<0, 1>>]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ terminated' = terminated

\* Leader becomes idle with zero weight
LeaderBecomeIdleZeroWeight ==
    /\ active[Leader]
    /\ IsZeroWeight(weight[Leader])
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, messages, terminated>>

\* Leader detects termination: leader is idle and has accumulated total weight 1
DetectTermination ==
    /\ ~active[Leader]
    /\ IsOneWeight(weight[Leader])
    /\ messages = {}
    /\ ~terminated
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, weight, messages>>

\* Next state relation
Next ==
    \/ \E p, q \in Procs : Activate(p, q)
    \/ \E p, q \in Procs : SendWeight(p, q)
    \/ \E p \in Procs : \E msg \in messages : Receive(p, msg)
    \/ \E p \in Procs : BecomeIdle(p)
    \/ \E p \in Procs : BecomeIdleZeroWeight(p)
    \/ LeaderBecomeIdle
    \/ LeaderBecomeIdleZeroWeight
    \/ DetectTermination

\* Fairness: Weak fairness on all actions to ensure progress
Fairness ==
    /\ \A p, q \in Procs : WF_vars(Activate(p, q))
    /\ \A p, q \in Procs : WF_vars(SendWeight(p, q))
    /\ \A p \in Procs : \A msg \in {m \in messages : m[1] = p} : WF_vars(Receive(p, msg))
    /\ \A p \in Procs : WF_vars(BecomeIdle(p))
    /\ \A p \in Procs : WF_vars(BecomeIdleZeroWeight(p))
    /\ WF_vars(LeaderBecomeIdle)
    /\ WF_vars(LeaderBecomeIdleZeroWeight)
    /\ WF_vars(DetectTermination)

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* State constraint for model checking: bound denominators
StateConstraint ==
    /\ \A p \in Procs : weight[p][2] <= MaxDenom
    /\ \A msg \in messages : msg[2][2] <= MaxDenom

\* ====================