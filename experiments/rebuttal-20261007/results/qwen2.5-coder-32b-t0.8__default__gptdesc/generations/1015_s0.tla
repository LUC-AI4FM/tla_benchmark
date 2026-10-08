---------------------------- MODULE VoucherSpec ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS vouchers

VARIABLES state

(* --algorithm VoucherLifeCycle

variables state = {[v \in vouchers |-> "phantom"]};

fair process (v \in vouchers)
1: while TRUE do
2:     if state[v] = "phantom" then
3:         await /\ \/ state[v] = "phantom"
4:                \/ state[v] = "valid"
5:         state[v] := "valid"
6:     else if state[v] = "valid" then
7:         await TRUE;
8:         either
9:             await /\ \/ state[v] = "valid"
10:                    \/ state[v] = "redeemed"
11:                    \/ state[v] = "cancelled"
12:             state[v] := "redeemed"
13:         or
14:             await /\ \/ state[v] = "valid"
15:                    \/ state[v] = "redeemed"
16:                    \/ state[v] = "cancelled"
17:             state[v] := "cancelled"
18:         or
19:             await TRUE;
20:     else
21:         skip;

end process; *)

Init == state \in [vouchers -> {"phantom", "valid", "redeemed", "cancelled"}]

Next ==
    \/ /\ E v \in vouchers : state' = [state EXCEPT ![v] = "valid"] 
       /\ state[v] = "phantom"
    \/ /\ E v \in vouchers : state'[v] \in {"valid", "redeemed", "cancelled"}
       /\ state[v] = state'[v]

TypeOK == state \in [vouchers -> {"phantom", "valid", "redeemed", "cancelled"}]

Consistency == TRUE  \* Placeholder for any specific consistency invariants

Spec ==
    Init /\ [][Next]_<<v \in vouchers>> /\ WF_<<v \in vouchers>>(Next)

=============================================================================