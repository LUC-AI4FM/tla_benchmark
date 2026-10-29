---------------------------- MODULE PCRProtocol ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS DNA, PRIMER

ASSUME DNA # {} /\ IsFiniteSet(DNA)
ASSUME IsFiniteSet(PRIMER)

MaxCycles == 3

NoPrimer == CHOOSE x : x \notin PRIMER

Compatible(p, d) == p \in PRIMER /\ d \in DNA

TStates == {"free", "bound", "product"}
PStates == {"free", "bound", "used"}
Stages  == {"bind", "extend", "reset", "done"}

VARIABLES tState, pState, binding, stage, cycle, products

vars == <<tState, pState, binding, stage, cycle, products>>

TypeOK ==
    /\ tState \in [DNA -> TStates]
    /\ pState \in [PRIMER -> PStates]
    /\ binding \in [DNA -> PRIMER \cup {NoPrimer}]
    /\ stage \in Stages
    /\ cycle \in 0..MaxCycles
    /\ products \in 0..Cardinality(PRIMER)

FreeT == {d \in DNA : tState[d] = "free"}
FreeP == {p \in PRIMER : pState[p] = "free"}
UsedP == {p \in PRIMER : pState[p] = "used"}
BoundT == {d \in DNA : tState[d] = "bound"}

CanBind == \E d \in FreeT, p \in FreeP : Compatible(p, d)

Init ==
    /\ tState = [d \in DNA |-> "free"]
    /\ pState = [p \in PRIMER |-> "free"]
    /\ binding = [d \in DNA |-> NoPrimer]
    /\ stage = "bind"
    /\ cycle = 0
    /\ products = 0

Bind(d, p) ==
    /\ stage = "bind"
    /\ tState[d] = "free"
    /\ pState[p] = "free"
    /\ Compatible(p, d)
    /\ tState' = [tState EXCEPT ![d] = "bound"]
    /\ pState' = [pState EXCEPT ![p] = "bound"]
    /\ binding' = [binding EXCEPT ![d] = p]
    /\ UNCHANGED <<stage, cycle, products>>

EndBind ==
    /\ stage = "bind"
    /\ ~CanBind
    /\ stage' = "extend"
    /\ UNCHANGED <<tState, pState, binding, cycle, products>>

Extend(d) ==
    /\ stage = "extend"
    /\ tState[d] = "bound"
    /\ binding[d] \in PRIMER
    /\ tState' = [tState EXCEPT ![d] = "product"]
    /\ pState' = [pState EXCEPT ![binding[d]] = "used"]
    /\ products' = products + 1
    /\ UNCHANGED <<binding, stage, cycle>>

EndExtend ==
    /\ stage = "extend"
    /\ BoundT = {}
    /\ stage' = "reset"
    /\ UNCHANGED <<tState, pState, binding, cycle, products>>

Reset ==
    /\ stage = "reset"
    /\ tState' = [d \in DNA |-> "free"]
    /\ binding' = [d \in DNA |-> NoPrimer]
    /\ cycle' = cycle + 1
    /\ stage' = IF cycle + 1 < MaxCycles THEN "bind" ELSE "done"
    /\ UNCHANGED <<pState, products>>

Finished ==
    /\ stage = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E d \in DNA, p \in PRIMER : Bind(d, p)
    \/ EndBind
    \/ \E d \in DNA : Extend(d)
    \/ EndExtend
    \/ Reset
    \/ Finished

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: primers bind only to compatible templates; at most one primer per
\* template and no primer bound to two templates.
BindingSafety ==
    /\ \A d \in DNA : tState[d] = "bound" =>
           /\ binding[d] \in PRIMER
           /\ Compatible(binding[d], d)
           /\ pState[binding[d]] = "bound"
    /\ \A d1, d2 \in DNA :
           (d1 # d2 /\ binding[d1] \in PRIMER) => binding[d1] # binding[d2]

\* Conservation: molecule totals only change through extension.
Conservation ==
    /\ Cardinality(FreeP) + Cardinality({p \in PRIMER : pState[p] = "bound"})
         + Cardinality(UsedP) = Cardinality(PRIMER)
    /\ products = Cardinality(UsedP)
    /\ Cardinality(FreeT) + Cardinality(BoundT)
         + Cardinality({d \in DNA : tState[d] = "product"}) = Cardinality(DNA)

Invariants == TypeOK /\ BindingSafety /\ Conservation

\* Progress: every started cycle eventually completes.
Progress ==
    \A c \in 0..(MaxCycles - 1) : (cycle = c /\ stage = "bind") ~> (cycle = c + 1)

\* Amplification liveness: available resources yield new products.
Amplification ==
    \A n \in 0..Cardinality(PRIMER) :
        (products = n /\ stage = "bind" /\ CanBind) ~> (products > n)

Termination == <>(stage = "done")

=============================================================================