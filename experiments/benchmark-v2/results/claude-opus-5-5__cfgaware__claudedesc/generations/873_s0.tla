---------------------------- MODULE Slush ----------------------------
(***************************************************************************)
(* Specification of the Slush protocol, a simple probabilistic consensus  *)
(* algorithm from the Avalanche family. Nodes try to agree on a color     *)
(* (Red or Blue) by repeatedly sampling their peers.                      *)
(*                                                                         *)
(* Each node hosts two processes: a SlushLoop process that drives the     *)
(* consensus and a SlushQuery process that answers queries. A separate    *)
(* ClientRequest process gives initial colors to nodes that have none.    *)
(*                                                                         *)
(* No fairness conditions are given. Note that TLA+ cannot express the    *)
(* probabilistic convergence questions that are central to analyzing      *)
(* Slush. This spec only captures the possible behaviors.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,                 \* The set of nodes
  SlushLoopProcess,     \* The set of SlushLoop process identifiers
  SlushQueryProcess,    \* The set of SlushQuery process identifiers
  HostMapping,          \* Set of tuples relating processes to their nodes
  SlushIterationCount,  \* Number of iterations each SlushLoop runs
  SampleSetSize,        \* Number of peers sampled per iteration
  PickFlipThreshold,    \* Number of replies needed to flip color
  NoColor,              \* Placeholder for an unassigned color
  NoMessage             \* Placeholder for no message

ASSUME SlushIterationCount \in Nat
ASSUME SampleSetSize \in Nat
ASSUME PickFlipThreshold \in Nat

Red  == "Red"
Blue == "Blue"
Color == {Red, Blue}

ASSUME NoColor \notin Color

QueryMessageType      == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"

ClientRequestId == "ClientRequest"

QueryMessage ==
  [type  : {QueryMessageType},
   src   : SlushLoopProcess,
   dst   : SlushQueryProcess,
   color : Color]

QueryReplyMessage ==
  [type  : {QueryReplyMessageType},
   src   : SlushQueryProcess,
   dst   : SlushLoopProcess,
   color : Color]

Message == QueryMessage \cup QueryReplyMessage

ProcSet == SlushLoopProcess \cup SlushQueryProcess \cup {ClientRequestId}

\* The node that hosts a given process, derived from HostMapping.
HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node :
    \E t \in HostMapping :
      \E i, j \in DOMAIN t : t[i] = n /\ t[j] = pid

\* The query process hosted on a given node.
QueryProcOf(n) == CHOOSE p \in SlushQueryProcess : HostOf[p] = n

VARIABLES
  pick,         \* Each node's current color pick
  message,      \* Set of messages in transit
  sampleSet,    \* Process-local sample sets of the SlushLoop processes
  loopVariant,  \* Iteration counters of the SlushLoop processes
  pc            \* Program counters

vars == <<pick, message, sampleSet, loopVariant, pc>>

TypeInvariant ==
  /\ pick \in [Node -> Color \cup {NoColor}]
  /\ message \subseteq Message

Init ==
  /\ pick = [n \in Node |-> NoColor]
  /\ message = {}
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopVariant = [p \in SlushLoopProcess |-> 0]
  /\ pc = [p \in ProcSet |->
             IF p \in SlushLoopProcess THEN "RequireColorAssignment"
             ELSE IF p \in SlushQueryProcess THEN "QueryReplyLoop"
             ELSE "ClientRequestLoop"]

(***************************************************************************)
(* ClientRequest process                                                  *)
(***************************************************************************)
ClientRequestLoop ==
  /\ pc[ClientRequestId] = "ClientRequestLoop"
  /\ IF \E n \in Node : pick[n] = NoColor
       THEN \E n \in {m \in Node : pick[m] = NoColor} :
              \E c \in Color :
                /\ pick' = [pick EXCEPT ![n] = c]
                /\ pc' = pc
       ELSE /\ pc' = [pc EXCEPT ![ClientRequestId] = "Done"]
            /\ UNCHANGED pick
  /\ UNCHANGED <<message, sampleSet, loopVariant>>

ClientRequest == ClientRequestLoop

(***************************************************************************)
(* SlushLoop process                                                      *)
(***************************************************************************)
RequireColorAssignment(self) ==
  /\ pc[self] = "RequireColorAssignment"
  /\ pick[HostOf[self]] # NoColor
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
  /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

ExecuteSlushLoop(self) ==
  /\ pc[self] = "ExecuteSlushLoop"
  /\ IF loopVariant[self] < SlushIterationCount
       THEN \E s \in {S \in SUBSET (Node \ {HostOf[self]}) :
                        Cardinality(S) = SampleSetSize} :
              /\ sampleSet' = [sampleSet EXCEPT ![self] = s]
              /\ message' = message \cup
                   {[type  |-> QueryMessageType,
                     src   |-> self,
                     dst   |-> QueryProcOf(n),
                     color |-> pick[HostOf[self]]] : n \in s}
              /\ pc' = [pc EXCEPT ![self] = "CollectReplies"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED <<message, sampleSet>>
  /\ UNCHANGED <<pick, loopVariant>>

CollectReplies(self) ==
  LET replies == {m \in message :
                    m.type = QueryReplyMessageType /\ m.dst = self}
      CountOf(c) == Cardinality({m \in replies : m.color = c})
      host == HostOf[self]
  IN
  /\ pc[self] = "CollectReplies"
  /\ \A n \in sampleSet[self] :
       \E m \in replies : HostOf[m.src] = n
  /\ IF \E c \in Color : CountOf(c) >= PickFlipThreshold
       THEN \E c \in {d \in Color : CountOf(d) >= PickFlipThreshold} :
              pick' = [pick EXCEPT ![host] = c]
       ELSE UNCHANGED pick
  /\ message' = message \ replies
  /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
  /\ loopVariant' = [loopVariant EXCEPT ![self] = @ + 1]
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoop(self) ==
  \/ RequireColorAssignment(self)
  \/ ExecuteSlushLoop(self)
  \/ CollectReplies(self)

(***************************************************************************)
(* SlushQuery process                                                     *)
(***************************************************************************)
QueryReplyLoop(self) ==
  /\ pc[self] = "QueryReplyLoop"
  /\ \/ \E m \in message :
          /\ m.type = QueryMessageType
          /\ m.dst = self
          /\ LET host == HostOf[self]
                 newPick == IF pick[host] = NoColor
                              THEN [pick EXCEPT ![host] = m.color]
                              ELSE pick
             IN
             /\ pick' = newPick
             /\ message' = (message \ {m}) \cup
                  {[type  |-> QueryReplyMessageType,
                    src   |-> self,
                    dst   |-> m.src,
                    color |-> newPick[host]]}
          /\ pc' = pc
     \/ /\ \A p \in SlushLoopProcess : pc[p] = "Done"
        /\ ~\E m \in message : m.type = QueryMessageType /\ m.dst = self
        /\ pc' = [pc EXCEPT ![self] = "Done"]
        /\ UNCHANGED <<pick, message>>
  /\ UNCHANGED <<sampleSet, loopVariant>>

SlushQuery(self) == QueryReplyLoop(self)

(***************************************************************************)
(* Full specification                                                     *)
(***************************************************************************)
Terminating ==
  /\ \A self \in ProcSet : pc[self] = "Done"
  /\ UNCHANGED vars

Next ==
  \/ ClientRequest
  \/ \E self \in SlushLoopProcess : SlushLoop(self)
  \/ \E self \in SlushQueryProcess : SlushQuery(self)
  \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

=============================================================================