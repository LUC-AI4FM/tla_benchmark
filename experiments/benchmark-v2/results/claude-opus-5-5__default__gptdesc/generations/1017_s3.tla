------------------------------ MODULE VoucherTransfer ------------------------------
(***************************************************************************)
(* A voucher transfer protocol modeled as a simplified Two-Phase Commit.   *)
(* A Voucher Transaction Provider (VTP) coordinates a set of Source        *)
(* Holders (SH) and a set of Destination Holders (DH) in transferring a    *)
(* set of vouchers V.                                                      *)
(*                                                                         *)
(* Communication is modeled by the variable msgs. It is a set of messages  *)
(* that only grows. A message is "sent" by adding it to msgs. A message is *)
(* "received" when an enabling condition tests that it is in msgs.         *)
(* Several messages of the full protocol are omitted for simplicity:       *)
(*   - The VTP's request asking holders to prepare is not modeled. A       *)
(*     holder may prepare on its own initiative at any time.               *)
(*   - The "Aborted" message a holder sends when it aborts on its own is   *)
(*     not modeled. The VTP may abort at any time before it commits, so    *)
(*     the message is not needed.                                          *)
(*   - Acknowledgements of Commit and Abort messages are not modeled.      *)
(* The SH and DH sets are assumed to be disjoint.                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* The voucher life-cycle specification that this protocol implements.    *)
(* It is written as a submodule and imported below with INSTANCE.          *)
(***************************************************************************)
------------------------------ MODULE VoucherLifeCycle ------------------------------
CONSTANT V          \* The set of vouchers.

VARIABLES vState,   \* vState[v] is the state of voucher v.
          vlcState  \* vlcState[v] is the state of the life-cycle machine for v.

VTypeOK ==
  /\ vState \in [V -> {"valid", "transferred"}]
  /\ vlcState \in [V -> {"working", "done"}]

VInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]

(* A set S of valid vouchers is transferred in one atomic step.            *)
VTransfer(S) ==
  /\ S # {}
  /\ \A v \in S : vState[v] = "valid" /\ vlcState[v] = "working"
  /\ vState' = [v \in V |-> IF v \in S THEN "transferred" ELSE vState[v]]
  /\ vlcState' = [v \in V |-> IF v \in S THEN "done" ELSE vlcState[v]]

VNext == \E S \in SUBSET V : VTransfer(S)

VConsistent ==
  \A v \in V : vState[v] = "transferred" <=> vlcState[v] = "done"

VSpec == VInit /\ [][VNext]_<<vState, vlcState>>

THEOREM VSpec => [](VTypeOK /\ VConsistent)
=====================================================================================