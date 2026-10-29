------------------------- MODULE DuplicateNextStates -------------------------
EXTENDS Integers, FiniteSets

VARIABLE x

vars == <<x>>

Values  == {0, 1, 2, 3}
InitVal == 0

Init == x = InitVal

(***************************************************************************)
(* Alternatives leaving the initial value. Several produce the same       *)
(* successor state but differ syntactically.                              *)
(***************************************************************************)

\* Plain assignment: exactly one successor (x = 1).
A1 == x = 0 /\ x' = 1

\* Assignment placed BEFORE a disjunction. Only the first disjunct is true,
\* so one successor (x = 1). This duplicates A1.
A2 == x = 0 /\ x' = 1 /\ (TRUE \/ x = 3)

\* Disjunction placed BEFORE the assignment. Both disjuncts are true, so
\* evaluation that branches on each disjunct generates x = 1 twice.
A3 == x = 0 /\ (x = 0 \/ x # 3) /\ x' = 1

\* Assignment placed BEFORE a disjunction whose disjuncts are both true.
\* A checker that fully explores the disjunction yields x = 2 twice;
\* lazy (short-circuit) evaluation yields it once.
A4 == x = 0 /\ x' = 2 /\ (x = 0 \/ x = 0)

\* Membership in a set with a repeated element. The enumeration
\* collapses {2, 2} = {2}, so this yields one successor (x = 2).
A5 == x = 0 /\ x' \in {2, 2}

\* Conjunct wrapped in IF so the guard is not eagerly split into branches.
\* This yields one successor (x = 3).
A6 == x = 0 /\ IF x = 0 THEN x' = 3 ELSE FALSE

\* Return from any non-initial value. This keeps the system deadlock-free.
Reset == x # InitVal /\ x' = InitVal

Next == A1 \/ A2 \/ A3 \/ A4 \/ A5 \/ A6 \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Semantic characterisation and counting expectations                    *)
(***************************************************************************)

\* Semantic successor relation from old value o to new value n.
SemNext(o, n) ==
    \/ o = 0 /\ n \in {1, 2, 3}
    \/ o # 0 /\ n = 0

SemSuccessors(o) == {n \in Values : SemNext(o, n)}

\* Number of syntactic action alternatives that leave the initial state.
NumSyntacticAlternatives == 6

\* Number of successor states generated from Init when every satisfied
\* disjunct is branched on, before duplicates are removed:
\* A1:1 + A2:1 + A3:2 + A4:2 + A5:1 + A6:1 = 8.
ExpectedRawSuccessorsFromInit == 8

\* Number of distinct successor states from Init after duplicates are removed.
ExpectedDistinctSuccessorsFromInit == 3

\* Distinct states a checker should report: 0, 1, 2 and 3.
ExpectedDistinctStates == 4

\* Number of initial states.
ExpectedInitStates == 1

\* Named safety properties checked below.
NamedInvariants == {"TypeOK", "AtOneProp", "AtTwoProp", "AtThreeProp",
                    "CanLeaveInit", "SuccessorsSemantic"}

ASSUME Cardinality(SemSuccessors(InitVal)) = ExpectedDistinctSuccessorsFromInit
ASSUME Cardinality(Values) = ExpectedDistinctStates
ASSUME Cardinality({v \in Values : v = InitVal}) = ExpectedInitStates
ASSUME ExpectedRawSuccessorsFromInit > ExpectedDistinctSuccessorsFromInit
ASSUME Cardinality(NamedInvariants) = 6
ASSUME InitVal \in Values

(***************************************************************************)
(* Safety invariants                                                      *)
(***************************************************************************)

TypeOK == x \in Values

\* Predicates that hold only in specific states.
IsOne   == x = 1
IsTwo   == x = 2
IsThree == x = 3

AtOneProp   == IsOne   <=> (x = 1 /\ x \notin {0, 2, 3})
AtTwoProp   == IsTwo   <=> (x = 2 /\ x \notin {0, 1, 3})
AtThreeProp == IsThree <=> (x = 3 /\ x \notin {0, 1, 2})

\* From the initial value there is a transition that changes the variable.
CanLeaveInit == (x = InitVal) => ENABLED (Next /\ x' # x)

\* Every enabled next value agrees with the semantic successor relation.
SuccessorsSemantic == \A n \in Values : (ENABLED (Next /\ x' = n)) <=> SemNext(x, n)

Invariants ==
    /\ TypeOK
    /\ AtOneProp
    /\ AtTwoProp
    /\ AtThreeProp
    /\ CanLeaveInit
    /\ SuccessorsSemantic

(***************************************************************************)
(* Temporal properties                                                    *)
(***************************************************************************)

AlwaysTyped == []TypeOK

\* Liveness: the system eventually leaves the initial value.
LeaveInit == <>(x # InitVal)

\* Infinitely often the system is away from the initial value.
LeaveInitInfinitelyOften == []<>(x # InitVal)

\* Every step from the initial value changes the variable to 1, 2 or 3.
StepFromInit == [][(x = InitVal) => (x' \in SemSuccessors(InitVal))]_vars

THEOREM Spec => []Invariants
THEOREM Spec => LeaveInit
=============================================================================