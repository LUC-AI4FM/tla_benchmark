---------------------------- MODULE MC_ParReach ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    Nodes,
    \* @type: Str -> Set(Str);
    Succ,
    \* @type: Str;
    Root,
    \* @type: Set(Str);
    Procs

VARIABLES
    \* @type: Set(Str);
    marked,
    \* @type: Set(Str);
    vroot,
    \* @type: Str -> Str;
    pc,
    \* @type: Str -> Str;
    u,
    \* @type: Str -> Set(Str);
    toVroot

vars == << marked, vroot, pc, u, toVroot >>

\* Concrete model values bound by the configuration
NodesVal == {"n1", "n2", "n3"}
SuccVal  == [n \in NodesVal |-> NodesVal \ {n}]
RootVal  == "n1"
ProcsVal == {"p1", "p2"}

-----------------------------------------------------------------------------
\* Reachability computed as a least fixpoint over Succ
RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    LET T == S \cup UNION {Succ[n] : n \in S}
    IN  IF T = S THEN S ELSE ReachFrom(T)

Reachable == ReachFrom({Root})

-----------------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ vroot = {Root}
    /\ u = [p \in Procs |-> Root]
    /\ toVroot = [p \in Procs |-> {}]
    /\ pc = [p \in Procs |-> "a"]

a(self) ==
    /\ pc[self] = "a"
    /\ IF vroot # {}
         THEN \E v \in vroot :
                /\ u' = [u EXCEPT ![self] = v]
                /\ vroot' = vroot \ {v}
                /\ pc' = [pc EXCEPT ![self] = "b"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << u, vroot >>
    /\ UNCHANGED << marked, toVroot >>

b(self) ==
    /\ pc[self] = "b"
    /\ IF u[self] \notin marked
         THEN /\ marked' = marked \cup {u[self]}
              /\ toVroot' = [toVroot EXCEPT ![self] = Succ[u[self]]]
              /\ pc' = [pc EXCEPT ![self] = "c"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
              /\ UNCHANGED << marked, toVroot >>
    /\ UNCHANGED << vroot, u >>

c(self) ==
    /\ pc[self] = "c"
    /\ IF toVroot[self] # {}
         THEN \E w \in toVroot[self] :
                /\ vroot' = vroot \cup {w}
                /\ toVroot' = [toVroot EXCEPT ![self] = toVroot[self] \ {w}]
                /\ pc' = [pc EXCEPT ![self] = "c"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "a"]
              /\ UNCHANGED << vroot, toVroot >>
    /\ UNCHANGED << marked, u >>

p(self) == a(self) \/ b(self) \/ c(self)

Terminating ==
    /\ \A self \in Procs : pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Procs : p(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

-----------------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ vroot \subseteq Nodes
    /\ u \in [Procs -> Nodes]
    /\ toVroot \in [Procs -> SUBSET Nodes]
    /\ pc \in [Procs -> {"a", "b", "c", "Done"}]

Inv ==
    /\ TypeOK
    /\ marked \subseteq Reachable
    /\ vroot \subseteq Reachable
    /\ (\A q \in Procs : pc[q] = "Done") => (marked = Reachable)

=============================================================================