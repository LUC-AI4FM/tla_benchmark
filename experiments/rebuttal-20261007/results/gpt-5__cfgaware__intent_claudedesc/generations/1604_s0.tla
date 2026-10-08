----------------------------- MODULE ProceduralReturnDemo -----------------------------

EXTENDS Naturals, TLC

CONSTANT defaultInitValue

VARIABLES ret, out, pc

vars == << ret, out, pc >>

(*
PlusCal algorithm demonstrating procedural composition with simulated return values
via a shared variable `ret`. A single fair process calls two procedures in sequence:
- Add(a, b): computes a + b and writes the result into `ret`
- ToStr(n): for n = 10, writes the string "10" into `ret`

The process calls Add(3, 7), passes the result to ToStr, writes the final `ret`
to `out`, and asserts expected intermediate and final values.

--algorithm Demo
variables ret = defaultInitValue, out = defaultInitValue;

procedure Add(a, b)
begin AddStart:
    ret := a + b;
    assert ret = 10;
    return;
end procedure;

procedure ToStr(n)
begin ToStrStart:
    if n = 10 then
        ret := "10";
    else
        assert FALSE;
    end if;
    return;
end procedure;

fair process Main = "P"
variable tmp;
begin
    L0:
        call Add(3, 7);
    L1:
        tmp := ret;
    L2:
        call ToStr(tmp);
    L3:
        out := ret;
        assert out = "10";
    Done:
        skip;
end process;

end algorithm;
*)

Init ==
    /\ ret = defaultInitValue
    /\ out = defaultInitValue
    /\ pc = "L0"

L0 ==
    /\ pc = "L0"
    /\ ret' = 3 + 7
    /\ out' = out
    /\ pc' = "L1"
    /\ Assert(ret' = 10, "Addition result must be 10")

L1 ==
    /\ pc = "L1"
    /\ UNCHANGED ret
    /\ out' = out
    /\ pc' = "L2"

L2 ==
    /\ pc = "L2"
    /\ Assert(ret = 10, "Intermediate ret must be 10 before conversion")
    /\ ret' = "10"
    /\ out' = out
    /\ pc' = "L3"

L3 ==
    /\ pc = "L3"
    /\ UNCHANGED ret
    /\ out' = ret
    /\ pc' = "Done"
    /\ Assert(out' = "10", "Final output must be \"10\"")

Next ==
    L0 \/ L1 \/ L2 \/ L3

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================