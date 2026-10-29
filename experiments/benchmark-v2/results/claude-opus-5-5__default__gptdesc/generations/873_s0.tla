------------------------------- MODULE Slush -------------------------------
(***************************************************************************)
(* Specification of the Slush protocol, a simple consensus algorithm from  *)
(* the Avalanche family. Nodes hold colors. Each node runs:               *)
(*   - a loop process that repeatedly samples peers, queries them for     *)
(*     their color, and flips to the majority color of the sample if it   *)
(*     differs from its own;                                              *)
(*   - a query process that answers incoming queries with its current     *)
(*     color (adopting the querier's color first if it has none).         *)
(* A single client process assigns colors to uncolored nodes.             *)
(*                                                                         *)
(* NOTE: Slush is probabilistic in intent: its guarantees hold with high  *)
(* probability given random sampling. TLA+ is not probabilistic, so this  *)
(* model is mainly useful as executable pseudocode with basic temporal    *)
(* checking, such as termination of all processes.                        *)
(*                                                                         *)
(* The definitions below have the form of a translated PlusCal            *)
(* algorithm, with an explicit pc variable for each process.              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,                 \* The set of nodes
  SlushLoopProcess,     \* The set of loop process identifiers
  SlushQueryProcess,    \* The set of query process identifiers
  ClientProcess,        \* The identifier of the client process
  HostMapping,          \* A set of <<node, process>> pairs
  SlushIterationCount,  \* Number of loop iterations per node
  SampleSetSize         \* Number of peers sampled per iteration

Red == "red"
Blue == "blue"
Color == {Red, Blue}
NoColor == "none"

LoopHost(n) == {p \in SlushLoopProcess : <<n, p>> \in HostMapping}
QueryHost(n) == {p \in SlushQueryProcess : <<n, p>> \in HostMapping}

ASSUME
  /\ IsFiniteSet(Node)
  /\ Node # {}
  /\ SlushLoopProcess \cap SlushQueryProcess = {}
  /\ ClientProcess \notin SlushLoopProcess \cup SlushQueryProcess
  /\ HostMapping \subseteq Node \X (SlushLoopProcess \cup SlushQueryProcess)
  /\ \A p \in SlushLoopProcess \cup SlushQueryProcess :
        Cardinality({n \in Node : <<n, p>> \in HostMapping}) = 1
  /\ \A n \in Node : Cardinality(LoopHost(n)) = 1
  /\ \A n \in Node : Cardinality(QueryHost(n)) = 1
  /\ SlushIterationCount \in Nat
  /\ SampleSetSize \in Nat \ {0}
  /\ SampleSetSize < Cardinality(Node)

HostOf(pid) == CHOOSE n \in Node : <<n, pid>> \in HostMapping

ProcSet == SlushLoopProcess \cup SlushQueryProcess \cup {ClientProcess}

Message ==
  [type : {"query", "response"}, src : Node, dst : Node, color : Color]

Label ==
  { "RequireColorAssignment", "ExecuteSlushLoop", "GatherResponses",
    "QueryReplyLoop", "ClientRequest", "Done" }

VARIABLES
  message,      \* Set of in-flight messages
  color,        \* Current color of each node
  sampleSet,    \* Peers sampled by each loop process in this iteration
  loopVariant,  \* Iteration counter of each loop process
  pc            \* Program counter of each process

vars == <<message, color, sampleSet, loopVariant, pc>>

-----------------------------------------------------------------------------

Init ==
  /\ message = {}
  /\ color = [n \in Node |-> NoColor]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopVariant = [p \in SlushLoopProcess |-> 0]
  /\ pc = [self \in ProcSet |->
             CASE self \in SlushLoopProcess  -> "RequireColorAssignment"
               [] self \in SlushQueryProcess -> "QueryReplyLoop"
               [] OTHER                      -> "ClientRequest"]

-----------------------------------------------------------------------------
(* Loop process *)

RequireColorAssignment(self) ==
  /\ pc[self] = "RequireColorAssignment"
  /\ color[HostOf(self)] # NoColor
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
  /\ UNCHANGED <<message, color, sampleSet, loopVariant>>

ExecuteSlushLoop(self) ==
  LET host == HostOf(self) IN
  /\ pc[self] = "ExecuteSlushLoop"
  /\ IF loopVariant[self] < SlushIterationCount
       THEN \E s \in {ss \in SUBSET (Node \ {host}) :
                        Cardinality(ss) = SampleSetSize} :
              /\ sampleSet' = [sampleSet EXCEPT ![self] = s]
              /\ message' = message \cup
                   { [type |-> "query", src |-> host, dst |-> d,
                      color |-> color[host]] : d \in s }
              /\ pc' = [pc EXCEPT ![self] = "GatherResponses"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED <<message, sampleSet>>
  /\ UNCHANGED <<color, loopVariant>>

GatherResponses(self) ==
  LET host == HostOf(self)
      responses == {m \in message : m.type = "response" /\ m.dst = host}
      other == CHOOSE c \in Color : c # color[host]
      otherCount == Cardinality({m \in responses : m.color = other})
  IN
  /\ pc[self] = "GatherResponses"
  /\ {m.src : m \in responses} = sampleSet[self]
  /\ color' = IF 2 * otherCount > SampleSetSize
                THEN [color EXCEPT ![host] = other]
                ELSE color
  /\ message' = message \ responses
  /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
  /\ loopVariant' = [loopVariant EXCEPT ![self] = @ + 1]
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoop(self) ==
  \/ RequireColorAssignment(self)
  \/ ExecuteSlushLoop(self)
  \/ GatherResponses(self)

-----------------------------------------------------------------------------
(* Query process *)

QueryReplyLoop(self) ==
  LET host == HostOf(self) IN
  /\ pc[self] = "QueryReplyLoop"
  /\ IF \A p \in SlushLoopProcess : pc[p] = "Done"
       THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED <<message, color>>
       ELSE /\ \E q \in {m \in message : m.type = "query" /\ m.dst = host} :
                 /\ color' = IF color[host] = NoColor
                               THEN [color EXCEPT ![host] = q.color]
                               ELSE color
                 /\ message' = (message \ {q}) \cup
                      { [type |-> "response", src |-> host, dst |-> q.src,
                         color |-> color'[host]] }
            /\ UNCHANGED pc
  /\ UNCHANGED <<sampleSet, loopVariant>>

SlushQuery(self) == QueryReplyLoop(self)

-----------------------------------------------------------------------------
(* Client process *)

ClientRequest ==
  /\ pc[ClientProcess] = "ClientRequest"
  /\ IF \E n \in Node : color[n] = NoColor
       THEN /\ \E n \in {nd \in Node : color[nd] = NoColor} :
                 \E c \in Color :
                   color' = [color EXCEPT ![n] = c]
            /\ UNCHANGED pc
       ELSE /\ pc' = [pc EXCEPT ![ClientProcess] = "Done"]
            /\ UNCHANGED color
  /\ UNCHANGED <<message, sampleSet, loopVariant>>

SlushClient == ClientRequest

-----------------------------------------------------------------------------

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
  /\ \A self \in ProcSet : pc[self] = "Done"
  /\ UNCHANGED vars

Next ==
  \/ SlushClient
  \/ \E self \in SlushLoopProcess : SlushLoop(self)
  \/ \E self \in SlushQueryProcess : SlushQuery(self)
  \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A self \in SlushLoopProcess : WF_vars(SlushLoop(self))
  /\ \A self \in SlushQueryProcess : WF_vars(SlushQuery(self))
  /\ WF_vars(SlushClient)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

-----------------------------------------------------------------------------

TypeOK ==
  /\ message \subseteq Message
  /\ color \in [Node -> Color \cup {NoColor}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
  /\ loopVariant \in [SlushLoopProcess -> 0..SlushIterationCount]
  /\ pc \in [ProcSet -> Label]

THEOREM Spec => []TypeOK
THEOREM Spec => Termination

=============================================================================