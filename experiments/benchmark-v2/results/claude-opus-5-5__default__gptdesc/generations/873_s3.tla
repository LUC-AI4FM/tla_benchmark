------------------------------- MODULE Slush -------------------------------
(***************************************************************************)
(* Specification of the Slush protocol, a simple consensus algorithm from  *)
(* the Avalanche family, written as a PlusCal-style algorithm translated   *)
(* into TLA+.                                                              *)
(*                                                                         *)
(* Nodes hold colors. Each node has:                                       *)
(*   - a loop process that repeatedly queries a sample of its peers and    *)
(*     adopts a different color if enough of the sample reports it;        *)
(*   - a query process that answers incoming queries with its current      *)
(*     color, first adopting the querier's color if it is uncolored.       *)
(* A single client process assigns colors to nodes that are uncolored.     *)
(*                                                                         *)
(* NOTE: Slush is probabilistic in intent: its guarantees hold with high   *)
(* probability over random sampling. TLA+ is not a probabilistic language. *)
(* This model treats sampling as nondeterministic choice, so it is mainly  *)
(* useful as executable pseudocode plus basic temporal checking such as    *)
(* termination. It does not establish probabilistic convergence.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,                 \* The set of nodes
    Color,                \* The set of possible colors
    NoColor,              \* The value of an uncolored node
    SampleSize,           \* Number of peers queried in each round
    SlushThreshold,       \* Responses needed to flip color (alpha)
    SlushIterationCount   \* Number of query rounds per loop process

ASSUME NoColor \notin Color
ASSUME Color # {}
ASSUME SampleSize \in Nat /\ SampleSize >= 1
ASSUME SampleSize < Cardinality(Node)
ASSUME SlushThreshold \in Nat
ASSUME SlushThreshold > SampleSize \div 2 /\ SlushThreshold <= SampleSize
ASSUME SlushIterationCount \in Nat

(***************************************************************************
--algorithm Slush
variables
    color    = [n \in Node |-> NoColor],
    query    = [n \in Node |-> {}],
    response = [n \in Node |-> {}];

define
    LoopProcess   == {<<"loop", n>> : n \in Node}
    QueryProcess  == {<<"query", n>> : n \in Node}
    ClientProcess == {<<"client">>}
    AllLoopsDone  == \A l \in LoopProcess : pc[l] = "Done"
end define;

fair process SlushLoop \in LoopProcess
variables sampleSet = {}, iterations = 0;
begin
RequireColor:
    await color[self[2]] # NoColor;
    iterations := 1;
LoopCond:
    if iterations <= SlushIterationCount then
QuerySample:
        with sample \in {s \in SUBSET (Node \ {self[2]}) :
                            Cardinality(s) = SampleSize} do
            sampleSet := sample;
            query := [m \in Node |->
                IF m \in sample
                THEN query[m] \cup {[src |-> self[2], color |-> color[self[2]]]}
                ELSE query[m]];
        end with;
TallyResponses:
        await \A m \in sampleSet : \E r \in response[self[2]] : r.src = m;
        \* flip color if some other color reaches the threshold
        response[self[2]] := {};
        iterations := iterations + 1;
        goto LoopCond;
    end if;
end process;

fair process SlushQuery \in QueryProcess
begin
WaitForQuery:
    either
        await query[self[2]] # {};
        with q \in query[self[2]] do
            \* uncolored node adopts querier's color, then responds
        end with;
        goto WaitForQuery;
    or
        await AllLoopsDone;
    end either;
end process;

fair process Client \in ClientProcess
begin
AssignColorsToNodes:
    while \E n \in Node : color[n] = NoColor do
        with n \in {m \in Node : color[m] = NoColor}, c \in Color do
            color[n] := c;
        end with;
    end while;
end process;

end algorithm;
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES color, query, response, pc

(* define statement *)
LoopProcess   == {<<"loop", n>> : n \in Node}
QueryProcess  == {<<"query", n>> : n \in Node}
ClientProcess == {<<"client">>}
AllLoopsDone  == \A l \in LoopProcess : pc[l] = "Done"

VARIABLES sampleSet, iterations

vars == << color, query, response, pc, sampleSet, iterations >>

ProcSet == LoopProcess \cup QueryProcess \cup ClientProcess

Message == [src : Node, color : Color]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ query = [n \in Node |-> {}]
    /\ response = [n \in Node |-> {}]
    /\ sampleSet = [self \in LoopProcess |-> {}]
    /\ iterations = [self \in LoopProcess |-> 0]
    /\ pc = [self \in ProcSet |->
                CASE self \in LoopProcess   -> "RequireColor"
                  [] self \in QueryProcess  -> "WaitForQuery"
                  [] self \in ClientProcess -> "AssignColorsToNodes"]

(***************************************************************************)
(* Loop process actions                                                    *)
(***************************************************************************)
RequireColor(self) ==
    /\ pc[self] = "RequireColor"
    /\ color[self[2]] # NoColor
    /\ iterations' = [iterations EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "LoopCond"]
    /\ UNCHANGED << color, query, response, sampleSet >>

LoopCond(self) ==
    /\ pc[self] = "LoopCond"
    /\ IF iterations[self] <= SlushIterationCount
          THEN pc' = [pc EXCEPT ![self] = "QuerySample"]
          ELSE pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << color, query, response, sampleSet, iterations >>

QuerySample(self) ==
    LET node == self[2] IN
    /\ pc[self] = "QuerySample"
    /\ \E sample \in {s \in SUBSET (Node \ {node}) :
                          Cardinality(s) = SampleSize} :
          /\ sampleSet' = [sampleSet EXCEPT ![self] = sample]
          /\ query' = [m \in Node |->
                IF m \in sample
                THEN query[m] \cup {[src |-> node, color |-> color[node]]}
                ELSE query[m]]
    /\ pc' = [pc EXCEPT ![self] = "TallyResponses"]
    /\ UNCHANGED << color, response, iterations >>

TallyResponses(self) ==
    LET node  == self[2]
        Count(c) == Cardinality({r \in response[node] : r.color = c})
        flips == {c \in Color : c # color[node] /\ Count(c) >= SlushThreshold}
    IN
    /\ pc[self] = "TallyResponses"
    /\ \A m \in sampleSet[self] : \E r \in response[node] : r.src = m
    /\ color' = IF flips = {}
                  THEN color
                  ELSE [color EXCEPT ![node] = CHOOSE c \in flips : TRUE]
    /\ response' = [response EXCEPT ![node] = {}]
    /\ iterations' = [iterations EXCEPT ![self] = iterations[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "LoopCond"]
    /\ UNCHANGED << query, sampleSet >>

SlushLoop(self) ==
    \/ RequireColor(self)
    \/ LoopCond(self)
    \/ QuerySample(self)
    \/ TallyResponses(self)

(***************************************************************************)
(* Query process actions                                                   *)
(***************************************************************************)
WaitForQuery(self) ==
    LET node == self[2] IN
    /\ pc[self] = "WaitForQuery"
    /\ \/ /\ query[node] # {}
          /\ \E q \in query[node] :
                LET newColor == IF color[node] = NoColor
                                  THEN q.color
                                  ELSE color[node]
                IN
                /\ color' = [color EXCEPT ![node] = newColor]
                /\ response' = [response EXCEPT ![q.src] =
                                  response[q.src] \cup
                                    {[src |-> node, color |-> newColor]}]
                /\ query' = [query EXCEPT ![node] = query[node] \ {q}]
          /\ pc' = [pc EXCEPT ![self] = "WaitForQuery"]
       \/ /\ AllLoopsDone
          /\ pc' = [pc EXCEPT ![self] = "Done"]
          /\ UNCHANGED << color, query, response >>
    /\ UNCHANGED << sampleSet, iterations >>

SlushQuery(self) == WaitForQuery(self)

(***************************************************************************)
(* Client process actions                                                  *)
(***************************************************************************)
AssignColorsToNodes(self) ==
    /\ pc[self] = "AssignColorsToNodes"
    /\ IF \E n \in Node : color[n] = NoColor
          THEN /\ \E n \in {m \in Node : color[m] = NoColor} :
                    \E c \in Color :
                        color' = [color EXCEPT ![n] = c]
               /\ pc' = [pc EXCEPT ![self] = "AssignColorsToNodes"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ color' = color
    /\ UNCHANGED << query, response, sampleSet, iterations >>

Client(self) == AssignColorsToNodes(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ (\E self \in LoopProcess : SlushLoop(self))
    \/ (\E self \in QueryProcess : SlushQuery(self))
    \/ (\E self \in ClientProcess : Client(self))
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in LoopProcess : WF_vars(SlushLoop(self))
    /\ \A self \in QueryProcess : WF_vars(SlushQuery(self))
    /\ \A self \in ClientProcess : WF_vars(Client(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
LoopLabels   == {"RequireColor", "LoopCond", "QuerySample",
                 "TallyResponses", "Done"}
QueryLabels  == {"WaitForQuery", "Done"}
ClientLabels == {"AssignColorsToNodes", "Done"}

TypeInvariant ==
    /\ color \in [Node -> Color \cup {NoColor}]
    /\ query \in [Node -> SUBSET Message]
    /\ response \in [Node -> SUBSET Message]
    /\ sampleSet \in [LoopProcess -> SUBSET Node]
    /\ iterations \in [LoopProcess -> 0..(SlushIterationCount + 1)]
    /\ pc \in [ProcSet -> LoopLabels \cup QueryLabels \cup ClientLabels]
    /\ \A p \in LoopProcess : pc[p] \in LoopLabels
    /\ \A p \in QueryProcess : pc[p] \in QueryLabels
    /\ \A p \in ClientProcess : pc[p] \in ClientLabels

=============================================================================