------------------------------ MODULE Session9onebitMC ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the one-bit mutual exclusion algorithm.      *)
(* The original wrapper EXTENDS Session9onebit. This version includes      *)
(* that algorithm's definitions directly so the module parses on its own.  *)
(* It states mutual exclusion, deadlock/livelock freedom and               *)
(* starvation-freedom properties over the state variable pc.               *)
(***************************************************************************)
EXTENDS Integers, Naturals

CONSTANTS N, Procs

ASSUME Procs = 0..(N-1)

VARIABLES x, j, pc

vars == <<x, j, pc>>

(*************************** One-bit algorithm *****************************)

Init == /\ x  = [i \in Procs |-> FALSE]
        /\ j  = [i \in Procs |-> 0]
        /\ pc = [i \in Procs |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED <<x, j>>

e1(self) == /\ pc[self] = "e1"
            /\ x'  = [x EXCEPT ![self] = TRUE]
            /\ j'  = [j EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "e2"]

e2(self) == /\ pc[self] = "e2"
            /\ IF j[self] < self
                 THEN IF x[j[self]]
                        THEN /\ x'  = [x EXCEPT ![self] = FALSE]
                             /\ pc' = [pc EXCEPT ![self] = "e2w"]
                             /\ UNCHANGED j
                        ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                             /\ UNCHANGED <<x, pc>>
                 ELSE /\ j'  = [j EXCEPT ![self] = self + 1]
                      /\ pc' = [pc EXCEPT ![self] = "e3"]
                      /\ UNCHANGED x

e2w(self) == /\ pc[self] = "e2w"
             /\ ~ x[j[self]]
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED <<x, j>>

e3(self) == /\ pc[self] = "e3"
            /\ IF j[self] < N
                 THEN /\ ~ x[j[self]]
                      /\ j' = [j EXCEPT ![self] = j[self] + 1]
                      /\ UNCHANGED <<x, pc>>
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ UNCHANGED <<x, j>>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED <<x, j>>

exit(self) == /\ pc[self] = "exit"
              /\ x'  = [x EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED j

proc(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e2w(self)
                \/ e3(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars((pc[self] # "ncs") /\ proc(self))

(*************************** Model constants *******************************)

ConstN == 3

ConstProcs == 0..2

(*************************** Properties ************************************)

Trying == {"e1", "e2", "e2w", "e3"}

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

DeadAndLivelockFree ==
    (\E p \in Procs : pc[p] \in Trying) ~> (\E p \in Procs : pc[p] = "cs")

NoStarveProc0 == (pc[0] \in Trying) ~> (pc[0] = "cs")

\* Note: NoStarveProc1 is NOT satisfied by the one-bit algorithm.
NoStarveProc1 == (pc[1] \in Trying) ~> (pc[1] = "cs")

=============================================================================