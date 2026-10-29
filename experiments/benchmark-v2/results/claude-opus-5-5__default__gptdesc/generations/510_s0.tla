------------------------------- MODULE SpanningTreeRoot -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Nodes, Edges, root, MaxNodes

ASSUME EdgeAssump == \A e \in Edges : /\ e \subseteq Nodes
                                     /\ Cardinality(e) = 2

ASSUME RootAssump == root \in Nodes

ASSUME MaxNodesAssump == /\ MaxNodes \in Nat
                         /\ Cardinality(Nodes) <= MaxNodes

-----------------------------------------------------------------------------
(* Graph operators *)

Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

SetNbrs(S) == UNION {Nbrs(n) : n \in S}

(* Declarative definition: the smallest set containing S closed under SetNbrs *)
ReachableFrom(S) ==
  {n \in Nodes : \A T \in SUBSET Nodes :
                    (S \subseteq T /\ SetNbrs(T) \subseteq T) => n \in T}

(* Executable recursive reachability procedure *)
RECURSIVE RF(_, _)
RF(B, T) == IF B = {}
              THEN T
              ELSE LET newT == T \cup B
                   IN  RF(SetNbrs(B) \ newT, newT)

ReachableFromRF(S) == RF(S, {})

THEOREM RFTheorem ==
  ASSUME NEW S \in SUBSET Nodes
  PROVE  RF(S, {}) = ReachableFrom(S)

ASSUME ReachAssump == ReachableFrom({root}) = Nodes

(* Nodes reachable from S in at most k steps *)
RECURSIVE ReachWithin(_, _)
ReachWithin(S, k) == IF k = 0
                       THEN S
                       ELSE LET R == ReachWithin(S, k - 1)
                            IN  R \cup SetNbrs(R)

Dist(n) == CHOOSE d \in 0..MaxNodes :
              /\ n \in ReachWithin({root}, d)
              /\ (d = 0 \/ n \notin ReachWithin({root}, d - 1))

-----------------------------------------------------------------------------
(***************************************************************************
  Algorithm (PlusCal, informally):
  variables depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes],
            parent = [n \in Nodes |-> IF n = root THEN root ELSE NoNode],
            mail   = [n \in Nodes |-> IF n \in Nbrs(root)
                                         THEN {[from |-> root, depth |-> 0]}
                                         ELSE {}];
  process (node \in Nodes)
  { a: while (TRUE) {
         with (msg \in mail[self]) {
           mail[self] := mail[self] \ {msg};
           if (msg.depth + 1 < depth[self]) {
              depth[self] := msg.depth + 1;
              parent[self] := msg.from;
              send [from |-> self, depth |-> msg.depth + 1] to all Nbrs(self)
           } } } }
 ***************************************************************************)

NoNode == CHOOSE v : v \notin Nodes

Infinity == MaxNodes

Msg == [from : Nodes, depth : 0..MaxNodes]

VARIABLES depth, parent, mail, pc

vars == <<depth, parent, mail, pc>>

ProcSet == Nodes

Init == /\ depth  = [n \in Nodes |-> IF n = root THEN 0 ELSE Infinity]
        /\ parent = [n \in Nodes |-> IF n = root THEN root ELSE NoNode]
        /\ mail   = [n \in Nodes |-> IF n \in Nbrs(root)
                                        THEN {[from |-> root, depth |-> 0]}
                                        ELSE {}]
        /\ pc     = [self \in ProcSet |-> "a"]

a(self) ==
  /\ pc[self] = "a"
  /\ \E msg \in mail[self] :
        IF msg.depth + 1 < depth[self]
          THEN /\ depth'  = [depth  EXCEPT ![self] = msg.depth + 1]
               /\ parent' = [parent EXCEPT ![self] = msg.from]
               /\ mail'   = [m \in Nodes |->
                               IF m = self
                                 THEN mail[self] \ {msg}
                                 ELSE IF m \in Nbrs(self)
                                        THEN mail[m] \cup
                                               {[from |-> self, depth |-> msg.depth + 1]}
                                        ELSE mail[m]]
          ELSE /\ mail' = [mail EXCEPT ![self] = mail[self] \ {msg}]
               /\ UNCHANGED <<depth, parent>>
  /\ pc' = [pc EXCEPT ![self] = "a"]

node(self) == a(self)

Next == \E self \in Nodes : node(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ depth  \in [Nodes -> 0..MaxNodes]
          /\ parent \in [Nodes -> Nodes \cup {NoNode}]
          /\ mail   \in [Nodes -> SUBSET Msg]
          /\ pc     \in [ProcSet -> {"a"}]

DepthBound == \A n \in Nodes : depth[n] >= Dist(n)

MsgBound == \A n \in Nodes : \A msg \in mail[n] :
               /\ msg.from \in Nbrs(n)
               /\ msg.depth >= Dist(msg.from)

ParentOK == \A n \in Nodes :
              /\ (n = root) => (parent[n] = root /\ depth[n] = 0)
              /\ (n # root /\ depth[n] # Infinity) =>
                    /\ parent[n] \in Nbrs(n)
                    /\ depth[parent[n]] < depth[n]

Inv == TypeOK /\ DepthBound /\ MsgBound /\ ParentOK

Terminated == \A n \in Nodes : mail[n] = {}

SpanningTreeCorrect ==
  \A n \in Nodes :
     /\ depth[n] = Dist(n)
     /\ (n # root) => /\ parent[n] \in Nbrs(n)
                      /\ depth[parent[n]] = depth[n] - 1

PartialCorrectness == Terminated => SpanningTreeCorrect

(* Liveness properties *)

Termination == <>Terminated

Liveness == <>[]SpanningTreeCorrect

=============================================================================