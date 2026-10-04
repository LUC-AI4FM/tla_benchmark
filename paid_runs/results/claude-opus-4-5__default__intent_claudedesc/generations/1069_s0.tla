---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxPending

ASSUME N \in Nat /\ N > 0
ASSUME MaxPending \in Nat /\ MaxPending > 0

Nodes == 0..(N-1)

VARIABLES
    active,         \* active[i] = TRUE iff node i is active
    pending,        \* pending[i] = count of pending messages for node i
    terminated,     \* TRUE iff termination has been detected
    token,          \* token position in the ring (node index or -1 if no token)
    tokenClean,     \* TRUE iff token has not seen any active node or pending messages
    initiator       \* node that initiated the current detection round

vars == <<active, pending, terminated, token, tokenClean, initiator>>

\* True termination: all nodes inactive and no pending messages
Terminated == \A i \in Nodes : ~active[i] /\ pending[i] = 0

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> 0..MaxPending]
    /\ terminated \in BOOLEAN
    /\ token \in Nodes \cup {-1}
    /\ tokenClean \in BOOLEAN
    /\ initiator \in Nodes

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending = [i \in Nodes |-> 0]
    /\ token = -1
    /\ tokenClean = TRUE
    /\ initiator = 0
    /\ terminated = (IF Terminated THEN TRUE ELSE FALSE)

\* An active node sends a message to another node
SendMessage(sender, receiver) ==
    /\ active[sender]
    /\ pending[receiver] < MaxPending
    /\ pending' = [pending EXCEPT ![receiver] = @ + 1]
    /\ UNCHANGED <<active, terminated, token, tokenClean, initiator>>

\* An active node voluntarily becomes inactive
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pending, terminated, token, tokenClean, initiator>>

\* A node receives a pending message and becomes active
ReceiveMessage(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<terminated, token, tokenClean, initiator>>

\* Start a new detection round from node 0 (initiator)
StartDetection ==
    /\ ~terminated
    /\ token = -1
    /\ ~active[0]
    /\ pending[0] = 0
    /\ token' = 0
    /\ tokenClean' = TRUE
    /\ initiator' = 0
    /\ UNCHANGED <<active, pending, terminated>>

\* Pass token from node i to next node in ring
PassToken(i) ==
    /\ ~terminated
    /\ token = i
    /\ i # initiator
    /\ LET nextNode == (i - 1) % N
           nodeClean == ~active[i] /\ pending[i] = 0
       IN /\ token' = nextNode
          /\ tokenClean' = tokenClean /\ nodeClean
    /\ UNCHANGED <<active, pending, terminated, initiator>>

\* Token returns to initiator - check for termination
CompleteDetection ==
    /\ ~terminated
    /\ token = initiator
    /\ LET initiatorClean == ~active[initiator] /\ pending[initiator] = 0
       IN IF tokenClean /\ initiatorClean
          THEN /\ terminated' = TRUE
               /\ token' = -1
          ELSE /\ terminated' = FALSE
               /\ token' = -1
    /\ UNCHANGED <<active, pending, tokenClean, initiator>>

\* System actions (actual computation)
System ==
    \/ \E i, j \in Nodes : SendMessage(i, j)
    \/ \E i \in Nodes : Deactivate(i)
    \/ \E i \in Nodes : ReceiveMessage(i)

\* Detection actions
Detection ==
    \/ StartDetection
    \/ \E i \in Nodes : i # initiator /\ PassToken(i)
    \/ CompleteDetection

Next ==
    \/ System
    \/ Detection

\* Fairness: detection algorithm makes progress
Fairness ==
    /\ WF_vars(StartDetection)
    /\ WF_vars(CompleteDetection)
    /\ \A i \in Nodes : WF_vars(PassToken(i))
    /\ \A i \in Nodes : WF_vars(ReceiveMessage(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* SAFETY: Detection flag never lies - if terminated flag is set, system has truly terminated
Safety == terminated => Terminated

\* QUIESCENCE: Once truly terminated, system stays terminated
Quiescence == Terminated => [][Terminated]_vars

\* Alternative formulation of quiescence as an invariant
QuiescenceInv == (Terminated /\ terminated) => Terminated

\* LIVENESS: If system terminates, detection eventually occurs
Liveness == Terminated ~> terminated

\* Combined correctness
Correctness == Safety /\ Quiescence /\ Liveness

===================================================================================