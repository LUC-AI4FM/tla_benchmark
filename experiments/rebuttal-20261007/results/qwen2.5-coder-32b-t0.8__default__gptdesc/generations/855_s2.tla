---- MODULE PrisonersAndSwitches ----
EXTENDS Naturals, FiniteSets

CONSTANTS Prs, Counter

VARIABLES sA, sB, visits

Init == /\ sA = FALSE
        /\ sB = FALSE
        /\ visits = {}

Next ==
  LET chosenPrisoner \in Prs
      in \/ chosenPrisoner = Counter -> 
             (\/ /\ sA 
                 /\ sA' = FALSE 
                 /\ sB' = sB 
                 /\ visits' = visits \cup {chosenPrisoner}
              \/ /\ ~sA 
                 /\ sA' = sA 
                 /\ sB' = ~sB
                 /\ visits' = visits)
         \/ chosenPrisoner # Counter -> 
             (\/ /\ sA 
                 /\ sA' = sA 
                 /\ sB' = ~sB
                 /\ visits' = visits \cup {chosenPrisoner}
              \/ /\ ~sA 
                 /\ sA' = IF Cardinality(visits) < Cardinality(Prs) - 1 THEN TRUE ELSE sA
                 /\ sB' = ~sB
                 /\ visits' = visits \cup {chosenPrisoner})

Spec ==
  WF_vars_<<Chosen>>_<>Init /\ <>[TRUE]_<<Chosen>>_Next

Safety == [](Cardinality(visits) = Cardinality(Prs) =>UNCHANGED visits)

Liveness == <>(Cardinality(visits) = Cardinality(Prs))

WF_vars_<<Chosen>>_<>Init ==
  WF_vars_<<Chosen>>_(Init /\ \A p \in Prs: (p # Counter) -> <<p>>_<>(/\ ~sA
                                                                        /\ sB' = ~sB
                                                                        /\ visits' = visits))

WF_vars_<<Chosen>>_Next ==
  WF_vars_<<Chosen>>_Spec

====