------------------------------ MODULE ProcReturnPlusCal ------------------------------

EXTENDS Naturals

(*
--fair algorithm ReturnDemo
variables ret = "unset", out = "unset", tmp = "unset";

procedure Add(a, b)
begin
  A1: ret := a + b;
      return;
end procedure;

procedure IntToString(x)
begin
  S1: if x = 10 then
         ret := "10";
      else
         AssertBad: assert FALSE;
      end if;
      return;
end procedure;

process P \in {"proc"}
begin
  L1: call Add(3, 7);
  L2: tmp := ret;
  Assert1: assert tmp = 10;
  L3: call IntToString(tmp);
  L4: out := ret;
  Assert2: assert out = "10";
  Done: skip;
end process;

end algorithm
*)

VARIABLES pc, ret, out, tmp

vars == << pc, ret, out, tmp >>

Init ==
  /\ pc = "L1"
  /\ ret = "unset"
  /\ out = "unset"
  /\ tmp = "unset"

L1_to_L2 ==
  /\ pc = "L1"
  /\ ret' = 3 + 7
  /\ pc' = "L2"
  /\ UNCHANGED << out, tmp >>

L2_to_L3 ==
  /\ pc = "L2"
  /\ tmp' = ret
  /\ pc' = "L3"
  /\ UNCHANGED << out, ret >>

L3_to_L4 ==
  /\ pc = "L3"
  /\ tmp = 10
  /\ ret' = "10"
  /\ pc' = "L4"
  /\ UNCHANGED << out, tmp >>

L4_to_Done ==
  /\ pc = "L4"
  /\ out' = ret
  /\ pc' = "Done"
  /\ UNCHANGED << ret, tmp >>

Next ==
  L1_to_L2 \/ L2_to_L3 \/ L3_to_L4 \/ L4_to_Done

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

(*
Safety invariants reflecting the PlusCal assertions.
- After taking L2, tmp must be 10 before proceeding further.
- Upon completion, out must be the string "10".
*)
TypeOK ==
  /\ pc \in {"L1","L2","L3","L4","Done"}
  /\ ret \in ({"unset"} \cup Nat \cup {"10"})
  /\ tmp \in ({"unset"} \cup Nat)
  /\ out \in ({"unset"} \cup Nat \cup {"10"})

AssertAddOK ==
  (pc \in {"L3","L4","Done"}) => tmp = 10

AssertConvOK ==
  (pc = "Done") => out = "10"

(*
Liveness: the process must eventually reach the completed state.
*)
Liveness ==
  <> (pc = "Done")

=============================================================================