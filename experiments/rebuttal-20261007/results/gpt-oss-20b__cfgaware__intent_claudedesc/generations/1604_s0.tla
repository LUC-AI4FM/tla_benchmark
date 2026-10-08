------------------------------ MODULE Demo ------------------------------
EXTENDS Naturals, TLC

CONSTANT defaultInitValue

VARIABLES retVal, retStr, outVar, state

vars == {retVal, retStr, outVar, state}

\*--algorithm Demo
procedure Add(x, y)
begin
    retVal := x + y;
end procedure

procedure Convert(n)
begin
    if n = 10 then
        retStr := "10"
    else
        retStr := "unknown";
end procedure

process P
begin
    state := "start";
    outVar := defaultInitValue;
    retVal := 0;
    retStr := "";
    
    Add(3,7);
    state := "addDone";
    
    Convert(retVal);
    state := "convertDone";
    
    outVar := retStr;
    state := "finished";
    
    assert outVar = "10";
end process
--\*END algorithm

Spec == Init /\ [][Next]_vars

=============================================================================