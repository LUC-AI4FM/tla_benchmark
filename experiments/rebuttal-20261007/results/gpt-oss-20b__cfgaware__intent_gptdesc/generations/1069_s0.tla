------------------------------ MODULE TerminationDetection ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N, MaxMsgPerProc

VARIABLES state, inbox, transit, detection

(* --------------------------------------------------------------------------- *)
(* Type definitions and invariants                                            *)
Message == Nat
StateVal == {"active", "inactive"}

TypeInv ==
  /\ state \in [1..N -> StateVal]
  /\ inbox \in [1..N -> Seq(Message)]
  /\ transit \in [1..N -> Seq(Message)]
  /\ detection \in BOOLEAN
  /\ \A i \in 1..N : Len(inbox[i]) <= MaxMsgPerProc
  /\ \A i \in 1..N : Len(transit[i]) <= MaxMsgPerProc

(* --------------------------------------------------------------------------- *)
(* Initial state                                                               *)
Init ==
  /\ state   = [i \in 1..N |-> "inactive"]
  /\ inbox   = [i \in 1..N |-> << >>
  /\ transit = [i \in 1..N |-> << >>
  /\ detection = FALSE
  /\ TypeInv

(* --------------------------------------------------------------------------- *)
(* Global termination predicate                                               *)
Termination ==
  /\ \A i \in 1..N : state[i] = "inactive"
  /\ \A i \in 1..N : Len(inbox[i])   = 0
  /\ \A i \in 1..N : Len(transit[i]) = 0

(* --------------------------------------------------------------------------- *)
(* Actions                                                                    *)
Send(p, q) ==
  /\ p \in 1..N
  /\ q \in 1..N
  /\ state[p] = "active"
  /\ Len(inbox[q]) + Len(transit[q]) < MaxMsgPerProc
  /\ LET msg == 1 IN
     transit'   = [transit EXCEPT ![q] = Append(transit[q], msg)]
     state'     = state
     inbox'     = inbox
     detection' = detection

Receive(q) ==
  /\ q \in 1..N
  /\ Len(transit[q]) > 0
  /\ LET m == Head(transit[q]) IN
     inbox'   = [inbox EXCEPT ![q] = Append(inbox[q], m)]
     transit' = [transit EXCEPT ![q] = Tail(transit[q])]
     state'   = state
     detection'=detection

Deactivate(p) ==
  /\ p \in 1..N
  /\ state[p] = "active"
  /\ state'   = [state EXCEPT ![p] = "inactive"]
  /\ inbox'   = inbox
  /\ transit' = transit
  /\ detection'=detection

Detect ==
  /\ Termination
  /\ detection' = TRUE
  /\ state'     = state
  /\ inbox'     = inbox
  /\ transit'   = transit

(* --------------------------------------------------------------------------- *)
(* Next-state relation                                                        *)
Next == \/ \E p,q \in 1..N : Send(p, q)
        \/ \E q \in 1..N : Receive(q)
        \/ \E p \in 1..N : Deactivate(p)
        \/ Detect

(* --------------------------------------------------------------------------- *)
(* Specification                                                              *)
Spec ==
  Init
  /\ [][Next]_<<state, inbox, transit, detection>>
  /\ []TypeInv

(* --------------------------------------------------------------------------- *)
(* Properties to be checked                                                  *)
Safety == detection => Termination

Liveness == [](Termination => <> detection)

Quiescence == [](Termination => []Termination)
===============================================================================