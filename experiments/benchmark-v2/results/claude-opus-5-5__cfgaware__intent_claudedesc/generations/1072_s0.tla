---------------------------- MODULE EWD998ChanID ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Node
ASSUME NodeAssumption == IsFiniteSet(Node) /\ Node # {}

N == Cardinality(Node)

Color == {"white", "black"}

(* The token initiator, chosen arbitrarily but fixed. *)
Initiator == CHOOSE n \in Node : TRUE

(* Deterministic enumeration of the nodes, starting with the initiator. *)
RECURSIVE SetToSeq(_)
SetToSeq(S) ==
    IF S = {} THEN << >>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  << x >> \o SetToSeq(S \ {x})

Ord == << Initiator >> \o SetToSeq(Node \ {Initiator})

Nat2Node == [ i \in 0..N-1 |-> Ord[i+1] ]
Node2Nat == [ n \in Node |-> CHOOSE i \in 0..N-1 : Nat2Node[i] = n ]

(* The directed ring: the token moves from node i to node i-1, and the *)
(* initiator (index 0) sends a fresh token to node N-1.                *)
RingOfNodes == [ n \in Node |-> Nat2Node[(Node2Nat[n] + N - 1) % N] ]

VARIABLES
    active,
    color,
    counter,
    inbox,
    clock,
    passes

vars == << active, color, counter, inbox, clock, passes >>

-----------------------------------------------------------------------------
(* Auxiliary operators *)

Max(a, b) == IF a > b THEN a ELSE b

ZeroClock == [ m \in Node |-> 0 ]

Tick(n) == [ clock[n] EXCEPT ![n] = @ + 1 ]

Merge(n, vc) ==
    [ m \in Node |-> IF m = n
                     THEN Max(clock[n][m], vc[m]) + 1
                     ELSE Max(clock[n][m], vc[m]) ]

Remove(s, j) == [ k \in 1..(Len(s) - 1) |-> IF k < j THEN s[k] ELSE s[k+1] ]

Termination ==
    \A n \in Node :
        /\ ~ active[n]
        /\ \A j \in 1..Len(inbox[n]) : inbox[n][j].type # "pl"

terminationDetected ==
    \E j \in 1..Len(inbox[Initiator]) :
        /\ inbox[Initiator][j].type = "tok"
        /\ inbox[Initiator][j].color = "white"
        /\ counter[Initiator] + inbox[Initiator][j].q = 0
        /\ color[Initiator] = "white"
        /\ ~ active[Initiator]

(* Token passes are counted once the system has terminated. *)
TokenPasses == passes' = IF Termination THEN passes + 1 ELSE 0

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ \A n \in Node : inbox[n] \in Seq(
           [type : {"pl"}, src : Node, vc : [Node -> Nat]]
           \cup [type : {"tok"}, q : Int, color : Color, vc : [Node -> Nat]])
    /\ clock \in [Node -> [Node -> Nat]]
    /\ passes \in Nat

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ counter = [ n \in Node |-> 0 ]
    /\ inbox = [ n \in Node |->
                   IF n = Initiator
                   THEN << [type |-> "tok", q |-> 0, color |-> "black", vc |-> ZeroClock] >>
                   ELSE << >> ]
    /\ clock = [ n \in Node |-> ZeroClock ]
    /\ passes = 0

InitiateProbe ==
    /\ ~ active[Initiator]
    /\ \E j \in 1..Len(inbox[Initiator]) :
        LET tok == inbox[Initiator][j]
            nc  == Merge(Initiator, tok.vc)
        IN
        /\ tok.type = "tok"
        /\ \/ tok.color = "black"
           \/ color[Initiator] = "black"
           \/ counter[Initiator] + tok.q > 0
        /\ inbox' = [ inbox EXCEPT
                        ![Initiator] = Remove(@, j),
                        ![RingOfNodes[Initiator]] =
                            Append(@, [type |-> "tok", q |-> 0,
                                       color |-> "white", vc |-> nc]) ]
        /\ clock' = [ clock EXCEPT ![Initiator] = nc ]
    /\ color' = [ color EXCEPT ![Initiator] = "white" ]
    /\ TokenPasses
    /\ UNCHANGED << active, counter >>

PassToken(n) ==
    /\ n # Initiator
    /\ ~ active[n]
    /\ \E j \in 1..Len(inbox[n]) :
        LET tok == inbox[n][j]
            nc  == Merge(n, tok.vc)
        IN
        /\ tok.type = "tok"
        /\ inbox' = [ inbox EXCEPT
                        ![n] = Remove(@, j),
                        ![RingOfNodes[n]] =
                            Append(@, [type  |-> "tok",
                                       q     |-> tok.q + counter[n],
                                       color |-> IF color[n] = "black"
                                                 THEN "black" ELSE tok.color,
                                       vc    |-> nc]) ]
        /\ clock' = [ clock EXCEPT ![n] = nc ]
    /\ color' = [ color EXCEPT ![n] = "white" ]
    /\ TokenPasses
    /\ UNCHANGED << active, counter >>

System == InitiateProbe \/ \E n \in Node \ {Initiator} : PassToken(n)

SendMsg(n) ==
    /\ active[n]
    /\ counter' = [ counter EXCEPT ![n] = @ + 1 ]
    /\ \E to \in Node \ {n} :
        LET nc == Tick(n)
        IN /\ inbox' = [ inbox EXCEPT ![to] =
                           Append(@, [type |-> "pl", src |-> n, vc |-> nc]) ]
           /\ clock' = [ clock EXCEPT ![n] = nc ]
    /\ passes' = 0
    /\ UNCHANGED << active, color >>

RecvMsg(n) ==
    /\ \E j \in 1..Len(inbox[n]) :
        /\ inbox[n][j].type = "pl"
        /\ inbox' = [ inbox EXCEPT ![n] = Remove(@, j) ]
        /\ clock' = [ clock EXCEPT ![n] = Merge(n, inbox[n][j].vc) ]
    /\ counter' = [ counter EXCEPT ![n] = @ - 1 ]
    /\ active' = [ active EXCEPT ![n] = TRUE ]
    /\ color' = [ color EXCEPT ![n] = "black" ]
    /\ passes' = 0

Deactivate(n) ==
    /\ active[n]
    /\ active' = [ active EXCEPT ![n] = FALSE ]
    /\ clock' = [ clock EXCEPT ![n] = Tick(n) ]
    /\ passes' = 0
    /\ UNCHANGED << color, counter, inbox >>

Environment == \E n \in Node : SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(* Model-checking support *)

EWD998ChanStateConstraint ==
    /\ \A n \in Node : counter[n] <= 3
    /\ \A n \in Node : Len(inbox[n]) <= 3

View ==
    << active, color, counter,
       [ n \in Node |-> [ j \in DOMAIN inbox[n] |-> [inbox[n][j] EXCEPT !.vc = 0] ] ],
       passes >>

-----------------------------------------------------------------------------
(* Properties *)

EWD998Safe == [](terminationDetected => Termination)

EWD998Live == Termination ~> terminationDetected

Max3TokenRounds == [](passes <= 3 * N)

-----------------------------------------------------------------------------
(* Refinement of the natural-number-indexed EWD998Chan specification *)

Strip(m) ==
    IF m.type = "pl"
    THEN [type |-> "pl"]
    ELSE [type |-> "tok", q |-> m.q, color |-> m.color]

EWD998Chan == INSTANCE EWD998Chan WITH
    N       <- N,
    active  <- [ i \in 0..N-1 |-> active[Nat2Node[i]] ],
    color   <- [ i \in 0..N-1 |-> color[Nat2Node[i]] ],
    counter <- [ i \in 0..N-1 |-> counter[Nat2Node[i]] ],
    inbox   <- [ i \in 0..N-1 |->
                   [ j \in 1..Len(inbox[Nat2Node[i]]) |-> Strip(inbox[Nat2Node[i]][j]) ] ]

EWD998ChanSpec == EWD998Chan!Spec

=============================================================================