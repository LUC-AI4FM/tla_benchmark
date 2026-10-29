------------------------------ MODULE SpanTreeReach ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Nodes, Edges, root, MaxNodes

-----------------------------------------------------------------------------
(* Graph operators                                                         *)
-----------------------------------------------------------------------------
Nbrs(n) == {m \in Nodes : {m, n} \in Edges}

SetNbrs(S) == UNION {Nbrs(n) : n \in S}

(* Declarative definition of the set of nodes reachable from S *)
ReachableFrom(S) ==
  LET R[i \in Nat] == IF i = 0 THEN S
                      ELSE R[i-1] \cup SetNbrs(R[i-1])
  IN  UNION {R[i] : i \in Nat}

(* Executable recursive reachability procedure *)
RECURSIVE RFRec(_, _)
RFRec(Explored, Front) ==
  IF Front = {} THEN Explored
  ELSE LET Exp == Explored \cup Front
       IN  RFRec(Exp, SetNbrs(Front) \ Exp)

RF(S) == RFRec({}, S)

-----------------------------------------------------------------------------
ASSUME EdgeAssump  == \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
ASSUME RootAssump  == root \in Nodes
ASSUME MaxAssump   == (MaxNodes \in Nat) /\ (Cardinality(Nodes) <= MaxNodes)
ASSUME ReachAssump == Nodes \subseteq ReachableFrom({root})

THEOREM RFEquiv == \A S \in SUBSET Nodes : RF(S) = ReachableFrom(S)

-----------------------------------------------------------------------------
(***************************************************************************
--algorithm SpanTree {
  variables mom    = [n \in Nodes |-> n],
            dist   = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes],
            msgs   = [n \in Nodes |-> {}],
            toSend = [n \in Nodes |-> IF n = root THEN Nbrs(root) ELSE {}];
  fair process (p \in Nodes) {
    a: while (TRUE) {
         either { with (m \in msgs[self]) {
                    if (m[1] < dist[self]) {
                      dist[self] := m[1];
                      mom[self]  := m[2];
                      toSend[self] := Nbrs(self) \ {m[2]} };
                    msgs[self] := msgs[self] \ {m} } }
         or     { with (k \in toSend[self]) {
                    msgs[k] := msgs[k] \cup {<<dist[self] + 1, self>>};
                    toSend[self] := toSend[self] \ {k} } }
       }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES mom, dist, msgs, toSend

vars == << mom, dist, msgs, toSend >>

ProcSet == Nodes

Init ==
  /\ mom    = [n \in Nodes |-> n]
  /\ dist   = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxNodes]
  /\ msgs   = [n \in Nodes |-> {}]
  /\ toSend = [n \in Nodes |-> IF n = root THEN Nbrs(root) ELSE {}]

Receive(self) ==
  \E m \in msgs[self] :
     /\ IF m[1] < dist[self]
          THEN /\ dist'   = [dist EXCEPT ![self] = m[1]]
               /\ mom'    = [mom EXCEPT ![self] = m[2]]
               /\ toSend' = [toSend EXCEPT ![self] = Nbrs(self) \ {m[2]}]
          ELSE UNCHANGED << dist, mom, toSend >>
     /\ msgs' = [msgs EXCEPT ![self] = msgs[self] \ {m}]

Send(self) ==
  \E k \in toSend[self] :
     /\ msgs'   = [msgs EXCEPT ![k] = msgs[k] \cup {<<dist[self] + 1, self>>}]
     /\ toSend' = [toSend EXCEPT ![self] = toSend[self] \ {k}]
     /\ UNCHANGED << mom, dist >>

p(self) == Receive(self) \/ Send(self)

Terminating ==
  /\ \A self \in ProcSet : msgs[self] = {} /\ toSend[self] = {}
  /\ UNCHANGED vars

Next == (\E self \in Nodes : p(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(p(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------
TypeOK ==
  /\ mom    \in [Nodes -> Nodes]
  /\ dist   \in [Nodes -> Nat]
  /\ msgs   \in [Nodes -> SUBSET (Nat \X Nodes)]
  /\ toSend \in [Nodes -> SUBSET Nodes]

Done == \A n \in Nodes : msgs[n] = {} /\ toSend[n] = {}

(* Partial correctness invariant on the tree being built *)
Inv ==
  /\ dist[root] = 0
  /\ mom[root] = root
  /\ \A n \in Nodes \ {root} :
        dist[n] < MaxNodes => /\ mom[n] \in Nbrs(n)
                              /\ dist[mom[n]] < dist[n]

(* When finished, every node points to a neighbor one step closer to root *)
PostCondition ==
  Done => \A n \in Nodes \ {root} :
             /\ mom[n] \in Nbrs(n)
             /\ dist[n] = dist[mom[n]] + 1

Correct == PostCondition

(* Liveness: the algorithm eventually terminates and the result is stable *)
Termination == <>Done
Liveness    == <>[](Done /\ PostCondition)
=============================================================================