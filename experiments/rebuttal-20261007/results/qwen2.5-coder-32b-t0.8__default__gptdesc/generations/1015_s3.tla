---- MODULE VoucherLifecycle ----

EXTENDS Integers, FiniteSets, TLC

CONSTANTS vouchers

VARIABLES voucherStates

PHANTOM == "phantom"
VALID == "valid"
REDEEMED == "redeemed"
CANCELLED == "cancelled"

(* --algorithm VoucherLifecycle
variables voucherStates = [v \in vouchers |-> PHANTOM]
begin
    Init;
    while TRUE do
        with
            action \in {"issue", "transfer", "redeem", "cancel"} do
                if action = "issue" then
                    with v \in vouchers, vState \in voucherStates:PHANTOM do
                        voucherStates[v] := VALID
                    end with;
                else if action = "transfer" then
                    with v \in vouchers, vState \in voucherStates:VALID do
                        (* transfer is a stuttering action *)
                    end with;
                else if action = "redeem" then
                    with v \in vouchers, vState \in voucherStates:VALID do
                        voucherStates[v] := REDEEMED
                    end with;
                else if action = "cancel" then
                    with v \in vouchers, vState \in voucherStates:VALID do
                        voucherStates[v] := CANCELLED
                    end with;
                end if;
            end with;
        end while;
end algorithm *)

TypeCorrectness ==
    /\ voucherStates \in [vouchers -> {PHANTOM, VALID, REDEEMED, CANCELLED}]
    /\ \A v \in vouchers: \/ voucherStates[v] = PHANTOM
                              \/ voucherStates[v] = VALID
                              \/ voucherStates[v] = REDEEMED
                              \/ voucherStates[v] = CANCELLED

Init ==
    voucherStates = [v \in vouchers |-> PHANTOM]

Issue(v) ==
    /\ voucherStates[v] = PHANTOM
    /\ voucherStates' = [voucherStates EXCEPT ![v] = VALID]

Transfer(v) ==
    /\ voucherStates[v] = VALID
    /\ voucherStates' = voucherStates

Redeem(v) ==
    /\ voucherStates[v] = VALID
    /\ voucherStates' = [voucherStates EXCEPT ![v] = REDEEMED]

Cancel(v) ==
    /\ voucherStates[v] = VALID
    /\ voucherStates' = [voucherStates EXCEPT ![v] = CANCELLED]

Next ==
    \E v \in vouchers:
        \/ Issue(v)
        \/ Transfer(v)
        \/ Redeem(v)
        \/ Cancel(v)

Spec ==
    WF_next(Init, Next) /\
    TypeCorrectness /\ []TypeCorrectness

====