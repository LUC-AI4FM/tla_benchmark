---------------------------- MODULE MC_bcastFolklore ----------------------------
(***************************************************************************)
(* Folklore reliable broadcast with crash failures, with Apalache type      *)
(* annotations. The behavior of the bcastFolklore base module is inlined   *)
(* here so that this module parses on its own.                              *)
(*                                                                         *)
(* Model-checking configuration: N = 4, T = 1, F = 1.                      *)
(* Invariant checked: TypeOK. Specification: Spec.                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int;
    T,
    \* @type: Int;
    F

VARIABLES
    \* @type: Set(Int);
    Corr,
    \* @type: Int;
    nCrashed,
    \* @type: Int -> Str;
    pc,
    \* @type: Int -> Set(<<Int, Str>>);
    rcvd,
    \* @type: Set(<<Int, Str>>);
    sent

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat
ASSUME (N > 2 * T) /\ (T >= F) /\ (F >= 0)

\* Concrete values used by the model-checking configuration
ConstInit == N = 4 /\ T = 1 /\ F = 1

Proc == 1 .. N
M == { "ECHO" }

vars == << pc, rcvd, sent, nCrashed, Corr >>

(* A process receives a message that was sent but that it has not yet received. *)
Receive(self) ==
    \E r \in Proc \X M :
        /\ r \in (sent \ rcvd[self])
        /\ rcvd' = [ i \in Proc |->
                        IF i # self THEN rcvd[i] ELSE rcvd[self] \cup { r } ]

(* A process with initial value V1 broadcasts ECHO and accepts. *)
UponV1(self) ==
    /\ pc[self] = "V1"
    /\ pc' = [pc EXCEPT ![self] = "AC"]
    /\ sent' = sent \cup { << self, "ECHO" >> }
    /\ nCrashed' = nCrashed
    /\ Corr' = Corr

(* A process that has received some message relays ECHO and accepts. *)
UponAccept(self) ==
    /\ (pc[self] = "V0" \/ pc[self] = "V1")
    /\ rcvd'[self] # {}
    /\ pc' = [pc EXCEPT ![self] = "AC"]
    /\ sent' = sent \cup { << self, "ECHO" >> }
    /\ nCrashed' = nCrashed
    /\ Corr' = Corr

(* A process crashes, as long as fewer than F processes have crashed. *)
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
    /\ pc \in [ Proc -> { "V0", "V1" } ]
    /\ rcvd = [ i \in Proc |-> {} ]
    /\ nCrashed = 0
    /\ Corr = Proc

Next == \E self \in Corr : Step(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E self \in Corr :
                  /\ Receive(self)
                  /\ \/ UponV1(self)
                     \/ UponAccept(self)
                     \/ UNCHANGED << pc, sent, nCrashed, Corr >>)

(***************************************************************************)
(* Safety: type correctness                                                *)
(***************************************************************************)
TypeOK ==
    /\ sent \subseteq Proc \X M
    /\ pc \in [ Proc -> { "V0", "V1", "AC", "CR" } ]
    /\ rcvd \in [ Proc -> SUBSET (Proc \X M) ]
    /\ nCrashed \in 0 .. N
    /\ Corr \subseteq Proc

(***************************************************************************)
(* Properties of the base folklore broadcast module                        *)
(***************************************************************************)
\* If no correct process starts with V1, no correct process ever accepts.
Unforg ==
    (\A i \in Corr : pc[i] # "V1") => [](\A i \in Corr : pc[i] # "AC")

\* If all correct processes start with V1, eventually some correct process accepts.
Correctness ==
    (\A i \in Corr : pc[i] = "V1") => <>(\E i \in Corr : pc[i] = "AC")

\* If some correct process accepts, eventually all correct processes accept.
Agreement ==
    []((\E i \in Corr : pc[i] = "AC") => <>(\A i \in Corr : pc[i] = "AC"))

=============================================================================