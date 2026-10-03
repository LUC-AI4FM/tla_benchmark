---- MODULE OneStepByz ----
EXTENDS Naturals, FiniteSets

(*
  One-step Byzantine consensus (Dobre & Suri, DSN 2006) abstract model.
  Constants:
    - N: number of processes
    - F: max number of Byzantine processes tolerated
    - T: threshold parameter for deciding a value
*)

CONSTANTS N, F, T

ASSUME
  /\ N \in Nat /\ N >= 1
  /\ F \in Nat /\ F < N
  /\ T \in Nat /\ T >= 1 /\ T <= N

Proc   == 1..N
Values == {0, 1}
NoDec  == -1

VARIABLES
  proposals,   \* [Proc -> Values]
  faulty,      \* SUBSET Proc
  rc,          \* [Proc -> [Values -> 0..N]]: received message counts per receiver and value
  decided,     \* [Proc -> (Values \cup {NoDec})]
  state,       \* [Proc -> {"proposing", "decided", "faulty"}]
  sentCount,   \* total number of messages sent (idealized)
  stepped      \* has the one-step round been performed?

vars == << proposals, faulty, rc, decided, state, sentCount, stepped >>

TypeOK ==
  /\ proposals \in [Proc -> Values]
  /\ faulty \subseteq Proc
  /\ Cardinality(faulty) <= F
  /\ rc \in [Proc -> [Values -> 0..N]]
  /\ \A p \in Proc: rc[p][0] + rc[p][1] <= N
  /\ decided \in [Proc -> (Values \cup {NoDec})]
  /\ state \in [Proc -> {"proposing", "decided", "faulty"}]
  /\ sentCount \in 0..(N * N)
  /\ stepped \in BOOLEAN

CommonInit ==
  /\ faulty = {}
  /\ rc = [p \in Proc |-> [v \in Values |-> 0]]
  /\ decided = [p \in Proc |-> NoDec]
  /\ state = [p \in Proc |-> "proposing"]
  /\ sentCount = 0
  /\ stepped = FALSE

Init0 ==
  /\ proposals = [p \in Proc |-> 0]
  /\ CommonInit

Init1 ==
  /\ proposals = [p \in Proc |-> 1]
  /\ CommonInit

Init ==
  /\ proposals \in [Proc -> Values]
  /\ CommonInit

BecomeFaulty ==
  \E p \in Proc \ faulty:
    /\ Cardinality(faulty) < F
    /\ faulty' = faulty \cup {p}
    /\ proposals' = proposals
    /\ rc' = rc
    /\ decided' = decided
    /\ sentCount' = sentCount
    /\ stepped' = stepped
    /\ state' = [state EXCEPT ![p] = "faulty"]

Step ==
  /\ ~stepped
  /\ LET Corr == Proc \ faulty
         CountCorrVal(v) == Cardinality({ q \in Corr: proposals[q] = v })
     IN
       \E Byz \in [Proc -> [faulty -> Values]]:
         /\ rc' =
              [ p \in Proc |->
                [ v \in Values |->
                    CountCorrVal(v)
                  + Cardinality({ q \in faulty: Byz[p][q] = v })
                ]
              ]
         /\ sentCount' = N * N
         /\ decided' =
              [ p \in Proc |->
                IF p \in Corr THEN
                  IF rc'[p][1] >= T THEN 1
                  ELSE IF rc'[p][0] >= T THEN 0
                  ELSE proposals[p]
                ELSE
                  decided[p]
              ]
         /\ state' =
              [ p \in Proc |->
                IF p \in Corr THEN "decided" ELSE "faulty"
              ]
         /\ proposals' = proposals
         /\ faulty' = faulty
         /\ stepped' = TRUE

Next == BecomeFaulty \/ Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

OneStep0_Ltl == Init0 /\ [][Next]_vars /\ WF_vars(Step)
OneStep1_Ltl == Init1 /\ [][Next]_vars /\ WF_vars(Step)

(*
  Safety predicate useful under all-1 initial proposals:
  Whenever a process is in state "decided", it decided value 1.
*)
AllDecideOne ==
  \A p \in Proc: state[p] = "decided" => decided[p] = 1

====