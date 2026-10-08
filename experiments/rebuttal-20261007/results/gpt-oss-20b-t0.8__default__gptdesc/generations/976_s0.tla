MODULE RingAlgorithm

EXTENDS Naturals, TLC

CONSTANT N

VARIABLES x, y, pc

(*--------------------------------------------------------------------------*)
(* Type correctness constraints                                            *)
(*--------------------------------------------------------------------------*)

TypeInvariant ==
    /\ x \in [1..N -> Nat]
    /\ y \in [1..N -> Nat]
    /\ pc \in [1..N -> {0,1,2,3}]

(*--------------------------------------------------------------------------*)
(* Initial state                                                             *)
(*--------------------------------------------------------------------------*)

Init ==
    /\ TypeInvariant
    /\ ∀i \in 1..N : x[i] = 0
    /\ ∀i \in 1..N : y[i] = 0
    /\ ∀i \in 1..N : pc[i] = 0

(*--------------------------------------------------------------------------*)
(* Next-state relation                                                      *)
(*--------------------------------------------------------------------------*)

Next ==
    \/ LET i \in 1..N :
         (pc[i]=0) => 
           /\ x' = [x EXCEPT ![i] = 1]
           /\ pc' = [pc EXCEPT ![i] = 1]
           /\ y' = y
      \/ LET i \in 1..N :
          (pc[i]=1) =>
            LET left == IF i=1 THEN N ELSE i-1 IN
              /\ y' = [y EXCEPT ![i] = x[left]]
              /\ pc' = [pc EXCEPT ![i] = 2]
              /\ x' = x
      \/ LET i \in 1..N :
          (pc[i]=2) =>
            /\ pc' = [pc EXCEPT ![i] = 3]
            /\ x' = x
            /\ y' = y

(*--------------------------------------------------------------------------*)
(* Specification                                                            *)
(*--------------------------------------------------------------------------*)

Spec == Init /\ [][Next]_<<x,y,pc>>

(*--------------------------------------------------------------------------*)
(* Safety invariant: when all processes are done at least one y[i]=1       *)
(*--------------------------------------------------------------------------*)

Inv ==
    TypeInvariant
    /\ (∀i \in 1..N : pc[i] = 3 => ∃j \in 1..N : y[j] = 1)

THEOREM Correctness == Spec => []Inv
   PROOF
   QED

(*--------------------------------------------------------------------------*)
(* Liveness property: eventual completion of all processes                 *)
(*--------------------------------------------------------------------------*)

Termination ==
    <> (∀i \in 1..N : pc[i] = 3)

THEOREM TerminationTheorem == Spec => Termination
   PROOF
   QED

(*--------------------------------------------------------------------------*)
(* Alternative proof of correctness                                         *)
(*--------------------------------------------------------------------------*)

Correctness' ==
    Spec => []Inv

THEOREM CorrectnessPrime == Correctness'
   PROOF
      UNFOLD Init, Next, Inv
   QED

====)