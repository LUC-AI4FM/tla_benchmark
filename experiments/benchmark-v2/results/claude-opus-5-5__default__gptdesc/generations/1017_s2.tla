------------------------------ MODULE VoucherTransfer ------------------------------
(***************************************************************************)
(* A voucher transfer protocol modeled as a simplified Two-Phase Commit.   *)
(* A Voucher Transaction Provider (VTP) acts as the transaction manager.   *)
(* The source holders (SH) and destination holders (DH) are the resource   *)
(* managers.                                                               *)
(*                                                                         *)
(* Communication is modeled by the variable msgs, a set of messages that   *)
(* only grows. A message is never removed, so it can be received any       *)
(* number of times and the set also models loss and duplication.           *)
(*                                                                         *)
(* Some messages are omitted for simplicity:                               *)
(*   - The VTP's "Prepare" request is not modeled. A holder may prepare    *)
(*     spontaneously.                                                      *)
(*   - A holder that chooses to abort sends no message. The VTP may abort  *)
(*     at any time before it decides to transfer.                          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

-------------------------------- MODULE VoucherLifeCycle --------------------------------
(***************************************************************************)
(* A simplified voucher life cycle covering the transfer of a voucher.     *)
(* A valid voucher in the "working" phase may be transferred, which        *)
(* completes ("done") its transfer life cycle. The voucher stays valid     *)
(* with its new holder.                                                    *)
(***************************************************************************)
CONSTANT V

VARIABLES vState, vlcState

VTypeOK ==
  /\ vState   \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VInit ==
  /\ vState   = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]

VTransfer(S) ==
  /\ S # {}
  /\ \A v \in S : /\ vState[v] = "valid"
                  /\ vlcState[v] = "working"
  /\ vlcState' = [v \in V |-> IF v \in S THEN "done" ELSE vlcState[v]]
  /\ UNCHANGED vState

VNext == \E S \in SUBSET V : VTransfer(S)

VConsistent ==
  \A v \in V : vlcState[v] = "done" => vState[v] = "valid"

VSpec == VInit /\ [][VNext]_<<vState, vlcState>>

THEOREM VSpec => [](VTypeOK /\ VConsistent)
=========================================================================================