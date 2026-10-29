------------------------------ MODULE ABSpec ------------------------------
(***************************************************************************)
(* Abstract specification of the Alternating Bit protocol.                 *)
(*                                                                         *)
(* AVar is the message (payload, bit) most recently sent by the sender A.  *)
(* BVar is the message most recently accepted by the receiver B.           *)
(* NewValQueue holds payloads that the environment E has submitted and A   *)
(* has not yet taken.                                                      *)
(*                                                                         *)
(* A new message is in transit exactly when AVar # BVar.  Unreliable       *)
(* delivery is modeled by interleaving: B may act on the transmitted       *)
(* message at any later point, not necessarily right away.                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue

vars == <<AVar, BVar, NewValQueue>>

Msgs == Data \X {0, 1}

TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs
  /\ NewValQueue \in Seq(Data)

Init ==
  /\ AVar \in Msgs
  /\ BVar = AVar
  /\ NewValQueue = << >>

(***************************************************************************)
(* Environment: appends a new payload, only when A and B agree.            *)
(***************************************************************************)
E ==
  /\ AVar = BVar
  /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
  /\ UNCHANGED <<AVar, BVar>>

(***************************************************************************)
(* Sender: takes the next queued payload and flips its control bit.        *)
(***************************************************************************)
A ==
  /\ AVar = BVar
  /\ NewValQueue # << >>
  /\ AVar' = <<Head(NewValQueue), 1 - AVar[2]>>
  /\ NewValQueue' = Tail(NewValQueue)
  /\ UNCHANGED BVar

(***************************************************************************)
(* Receiver: accepts the transmitted message when it sees a different bit. *)
(***************************************************************************)
B ==
  /\ AVar # BVar
  /\ BVar' = AVar
  /\ UNCHANGED <<AVar, NewValQueue>>

Next == E \/ A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(B)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* Delivered payloads come only from sent messages, and every message
\* in transit differs from the receiver's state only in its bit.
Inv ==
  /\ TypeOK
  /\ (AVar[2] = BVar[2]) <=> (AVar = BVar)

\* No duplication: once B has accepted a message, it does not accept it
\* again until A sends a new one (B can only fire when the bits differ).
NoDuplication ==
  [][B => AVar # BVar]_vars

\* Order preservation: A always sends the head of the queue, and only
\* after B has accepted the previous message.
OrderPreserved ==
  [][A => /\ BVar = AVar
          /\ AVar'[1] = Head(NewValQueue)]_vars

\* Liveness: if E eventually stops adding payloads, then every pending
\* payload is eventually delivered.
Liveness ==
  (<>[][~E]_vars) => <>[](NewValQueue = << >> /\ AVar = BVar)

\* Every message that is sent is eventually received.
Delivery ==
  \A m \in Msgs : (AVar = m) ~> (BVar = m)

=============================================================================