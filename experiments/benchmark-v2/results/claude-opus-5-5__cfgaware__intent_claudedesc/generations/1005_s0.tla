--------------------------- MODULE bcastFolklore ---------------------------
(***************************************************************************)
(* Folklore reliable broadcast with crash failures.                        *)
(* N processes, at most T faulty, F actual crashes (F <= T, N > 2T).       *)
(* A process with initial value V1 broadcasts ECHO and accepts.  A process *)
(* that receives any ECHO relays ECHO and accepts.  Crashed processes are  *)
(* in state "CR" and take no further steps.                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES Corr,      \* the set of correct (non-crashed) processes
          nCrashed,  \* the number of crashed processes
          pc,        \* the control state of each process
          rcvd,      \* messages received by each process
          sent       \* messages sent into the network

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat
ASSUME (N > 2 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M    == { "ECHO" }

vars == << pc, rcvd, sent, nCrashed, Corr >>

(* Receive a new subset of the messages sent so far *)
Receive(self) ==
  \E r \in SUBSET (Proc \X M):
      /\ r \subseteq sent
      /\ rcvd[self] \subseteq r
      /\ rcvd' = [rcvd EXCEPT ![self] = r]

(* A process that initially holds the message broadcasts it and accepts *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ nCrashed' = nCrashed
  /\ Corr' = Corr

(* A process that has received an ECHO relays it and accepts *)
UponAccept(self) ==
  /\ (pc[self] = "V0" \/ pc[self] = "V1")
  /\ rcvd'[self] # {}
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ nCrashed' = nCrashed
  /\ Corr' = Corr

(* A process crashes, as long as fewer than F processes have crashed *)
UponCrash(self) ==
  /\ nCrashed < F
  /\ pc[self] # "CR"
  /\ nCrashed' = nCrashed + 1
  /\ pc' = [pc EXCEPT ![self] = "CR"]
  /\ sent' = sent
  /\ Corr' = Corr \ { self }

Step(self) ==
  /\ Receive(self)
  /\ \/ UponV1(self)
     \/ UponAccept(self)
     \/ UponCrash(self)
     \/ UNCHANGED << pc, sent, nCrashed, Corr >>

Init ==
  /\ sent = {}
  /\ pc \in [Proc -> {"V0", "V1"}]
  /\ rcvd = [i \in Proc |-> {}]
  /\ nCrashed = 0
  /\ Corr = Proc

InitNoBcast == Init /\ pc \in [Proc -> {"V0"}]

Next == \E self \in Corr : Step(self)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E self \in Corr :
                      /\ Receive(self)
                      /\ \/ UponV1(self)
                         \/ UponAccept(self)
                         \/ UNCHANGED << pc, sent, nCrashed, Corr >>)

SpecNoBcast == InitNoBcast /\ [][Next]_vars
        /\ WF_vars(\E self \in Corr :
                      /\ Receive(self)
                      /\ \/ UponV1(self)
                         \/ UponAccept(self)
                         \/ UNCHANGED << pc, sent, nCrashed, Corr >>)

(***************************************************************************)
(* Type and safety invariants                                              *)
(***************************************************************************)
TypeOK ==
  /\ sent \subseteq Proc \X M
  /\ pc \in [Proc -> {"V0", "V1", "AC", "CR"}]
  /\ rcvd \in [Proc -> SUBSET (Proc \X M)]
  /\ nCrashed \in 0 .. N
  /\ Corr \in SUBSET Proc

FCrashedInv == nCrashed <= F /\ nCrashed <= T

CorrCrashConsistent ==
  /\ \A i \in Proc : (i \notin Corr) <=> (pc[i] = "CR")
  /\ Cardinality(Proc \ Corr) = nCrashed

(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

(* Unforgeability: if no correct process initially holds the message,     *)
(* no correct process ever accepts.                                         *)
Unforg ==
  (\A i \in Corr : pc[i] # "V1") => [](\A i \in Corr : pc[i] # "AC")

(* Validity / Correctness: if a correct process broadcasts, it eventually *)
(* delivers (accepts).                                                      *)
Correctness ==
  (\A i \in Corr : pc[i] = "V1") => <>(\E i \in Corr : pc[i] = "AC")

ValidityPerProc ==
  \A i \in Proc : (pc[i] = "V1") ~> (pc[i] = "AC" \/ pc[i] = "CR")

(* Agreement (relay): if some correct process accepts, then eventually   *)
(* all correct processes accept.                                           *)
Relay ==
  [](
     (\E i \in Corr : pc[i] = "AC")
       => <>(\A i \in Corr : pc[i] = "AC"))

(* Termination: every correct process eventually decides (accepts) or     *)
(* stays undecided only when nobody broadcast.                             *)
Termination ==
  <>(\A i \in Corr : pc[i] = "AC" \/ (\A j \in Corr : pc[j] = "V0"))

=============================================================================