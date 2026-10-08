------------------------------ MODULE RingTermination ------------------------------

EXTENDS Naturals

CONSTANT N

VARIABLES active, pending, terminationDetected


(*--------------------------------------------------------------------------*)
(*  Type checking of the state variables                                    *)
(*--------------------------------------------------------------------------*)

TypeOK ==
  active \in [1..N -> BOOLEAN] /\
  pending \in [1..N -> Nat] /\
  terminationDetected \in BOOLEAN


(*--------------------------------------------------------------------------*)
(*  Initial condition                                                      *)
(*--------------------------------------------------------------------------*)

Init ==
  active \in [1..N -> BOOLEAN] /\ 
  pending = [i \in 1..N |-> 0] /\
  terminationDetected = ~(\E i \in 1..N : active[i])


(*--------------------------------------------------------------------------*)
(*  Actions                                                                *)
(*--------------------------------------------------------------------------*)

Terminate ==
  \E i \in 1..N :
    active[i] /\ 
    (active' = [active EXCEPT ![i] = FALSE]) /\
    pending' = pending /\
    terminationDetected' =
      IF (\A j \in 1..N : ~active'[j] /\ pending'[j] = 0) THEN TRUE ELSE terminationDetected


SendMsg ==
  \E i \in 1..N :
    active[i] /\
    \E j \in 1..N :
      (pending' = [pending EXCEPT ![j] = pending[j]+1]) /\ 
      active' = active /\ 
      terminationDetected' = terminationDetected


RcvMsg ==
  \E i \in 1..N :
    pending[i] > 0 /\
    (pending' = [pending EXCEPT ![i] = pending[i]-1]) /\ 
    active' = [active EXCEPT ![i] = TRUE] /\ 
    terminationDetected' = terminationDetected


DetectTermination ==
  (\A i \in 1..N : ~active[i] /\ pending[i] = 0) /\
  terminationDetected' = TRUE /\
  active' = active /\ 
  pending' = pending


(*--------------------------------------------------------------------------*)
(*  Next-state relation                                                    *)
(*--------------------------------------------------------------------------*)

Next == Terminate \/ SendMsg \/ RcvMsg \/ DetectTermination


(*--------------------------------------------------------------------------*)
(*  Specification (initial condition, next-state relation, fairness)       *)
(*--------------------------------------------------------------------------*)

Spec ==
  Init /\ [][Next]_{active, pending, terminationDetected} /\ WF_A(DetectTermination)


(*--------------------------------------------------------------------------*)
(*  Properties                                                             *)
(*--------------------------------------------------------------------------*)

Safe ==
  terminationDetected => (\A i \in 1..N : ~active[i] /\ pending[i] = 0)

Live ==
  []( (\A i \in 1..N : ~active[i] /\ pending[i] = 0) => <> terminationDetected)

Quiescence ==
  []( (\A i \in 1..N : ~active[i] /\ pending[i] = 0) =>
      (\A i \in 1..N : ~active'[i] /\ pending'[i] = 0))

IndInv == TypeOK /\ Safe


=============================================================================