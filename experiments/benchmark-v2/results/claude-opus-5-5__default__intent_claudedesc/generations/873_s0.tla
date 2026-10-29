---------------------------- MODULE Slush ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    NodeCount,              \* number of nodes in the network
    SlushIterationCount,    \* number of sampling iterations each node performs
    SampleSize,             \* size of the random sample taken each iteration
    PickFlipThreshold       \* count required to flip a node's value

ASSUME NodeCountAssumption   == NodeCount \in Nat \ {0}
ASSUME IterationAssumption   == SlushIterationCount \in Nat
ASSUME SampleSizeAssumption  == SampleSize \in 1..(NodeCount - 1)
ASSUME ThresholdAssumption   == PickFlipThreshold \in 1..SampleSize

Node    == 1..NodeCount
Color   == {"Red", "Blue"}
NoColor == "NoColor"

PC == {"Ready", "Waiting", "Done"}

QueryMessage ==
    [type : {"Query"}, src : Node, dst : Node, color : Color]

ResponseMessage ==
    [type : {"Response"}, src : Node, dst : Node, color : Color]

Message == QueryMessage \cup ResponseMessage

Response == [src : Node, color : Color]

VARIABLES
    color,      \* color[n] : current value of node n (or NoColor)
    iter,       \* iter[n]  : number of completed sampling iterations of n
    pc,         \* pc[n]    : control state of node n
    sample,     \* sample[n]: set of nodes sampled in n's current iteration
    received,   \* received[n]: responses collected in n's current iteration
    msgs        \* set of in-flight messages (asynchronous network)

vars == <<color, iter, pc, sample, received, msgs>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ color    \in [Node -> Color \cup {NoColor}]
    /\ iter     \in [Node -> 0..SlushIterationCount]
    /\ pc       \in [Node -> PC]
    /\ sample   \in [Node -> SUBSET Node]
    /\ received \in [Node -> SUBSET Response]
    /\ msgs     \subseteq Message
    /\ \A n \in Node : pc[n] = "Waiting" => color[n] \in Color
    /\ \A n \in Node : pc[n] = "Done" => iter[n] = SlushIterationCount

-----------------------------------------------------------------------------
Init ==
    /\ color    = [n \in Node |-> NoColor]
    /\ iter     = [n \in Node |-> 0]
    /\ pc       = [n \in Node |-> IF SlushIterationCount = 0
                                     THEN "Done" ELSE "Ready"]
    /\ sample   = [n \in Node |-> {}]
    /\ received = [n \in Node |-> {}]
    /\ msgs     = {}

\* An external client assigns an initial value to an unassigned node.
ClientRequest(n, c) ==
    /\ color[n] = NoColor
    /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<iter, pc, sample, received, msgs>>

\* A colored node randomly selects a sample of other nodes and queries them.
SendQueries(n, S) ==
    /\ pc[n] = "Ready"
    /\ color[n] \in Color
    /\ iter[n] < SlushIterationCount
    /\ S \subseteq (Node \ {n})
    /\ Cardinality(S) = SampleSize
    /\ msgs' = msgs \cup
         {[type |-> "Query", src |-> n, dst |-> q, color |-> color[n]] : q \in S}
    /\ sample'   = [sample EXCEPT ![n] = S]
    /\ received' = [received EXCEPT ![n] = {}]
    /\ pc'       = [pc EXCEPT ![n] = "Waiting"]
    /\ UNCHANGED <<color, iter>>

\* A queried node responds with its current color; if uncolored, it first
\* adopts the color carried by the query.
RespondToQuery(m) ==
    /\ m \in msgs
    /\ m.type = "Query"
    /\ LET n        == m.dst
           newColor == IF color[n] = NoColor THEN m.color ELSE color[n]
       IN /\ color' = [color EXCEPT ![n] = newColor]
          /\ msgs'  = (msgs \ {m}) \cup
               {[type |-> "Response", src |-> n, dst |-> m.src,
                 color |-> newColor]}
    /\ UNCHANGED <<iter, pc, sample, received>>

\* A sampling node collects a response to its query.
ReceiveResponse(m) ==
    /\ m \in msgs
    /\ m.type = "Response"
    /\ pc[m.dst] = "Waiting"
    /\ m.src \in sample[m.dst]
    /\ received' = [received EXCEPT ![m.dst] =
                        @ \cup {[src |-> m.src, color |-> m.color]}]
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<color, iter, pc, sample>>

CountOf(n, c) == Cardinality({r \in received[n] : r.color = c})

\* Once all responses are in, the node tallies them and possibly flips.
Tally(n) ==
    /\ pc[n] = "Waiting"
    /\ Cardinality(received[n]) = SampleSize
    /\ LET Qualifying == {c \in Color : CountOf(n, c) >= PickFlipThreshold}
       IN IF Qualifying = {}
            THEN UNCHANGED color
            ELSE \E c \in Qualifying : color' = [color EXCEPT ![n] = c]
    /\ iter' = [iter EXCEPT ![n] = @ + 1]
    /\ pc'   = [pc EXCEPT ![n] =
                   IF iter[n] + 1 = SlushIterationCount THEN "Done" ELSE "Ready"]
    /\ sample'   = [sample EXCEPT ![n] = {}]
    /\ received' = [received EXCEPT ![n] = {}]
    /\ UNCHANGED msgs

Terminated ==
    /\ \A n \in Node : pc[n] = "Done"
    /\ msgs = {}

\* Stuttering after termination to avoid reporting deadlock.
Terminating ==
    /\ Terminated
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node, c \in Color : ClientRequest(n, c)
    \/ \E n \in Node, S \in SUBSET (Node \ {}) : SendQueries(n, S)
    \/ \E m \in msgs : RespondToQuery(m)
    \/ \E m \in msgs : ReceiveResponse(m)
    \/ \E n \in Node : Tally(n)
    \/ Terminating

Fairness ==
    /\ \A n \in Node :
          /\ WF_vars(\E c \in Color : ClientRequest(n, c))
          /\ WF_vars(\E S \in SUBSET Node : SendQueries(n, S))
          /\ WF_vars(Tally(n))
    /\ \A m \in Message :
          /\ WF_vars(RespondToQuery(m))
          /\ WF_vars(ReceiveResponse(m))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: well-formedness of all values and messages.
THEOREM Spec => []TypeOK

\* Liveness: the protocol eventually completes.
Termination == <>(\A n \in Node : pc[n] = "Done")

TerminationAndQuiescence == <>Terminated

THEOREM Spec => Termination
=============================================================================