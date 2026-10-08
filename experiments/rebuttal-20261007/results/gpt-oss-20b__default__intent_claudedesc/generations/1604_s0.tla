MODULE ProcReturnDemo
EXTENDS Naturals, Sequences, TLC

--algorithm ProcReturnDemo
variables pc, addResult, convResult, outputVar;

procedure AddProc(a,b)
  BEGIN
    addResult := a + b;
  END;

procedure ConvProc(n)
  BEGIN
    IF n = 10 THEN
      convResult := "10";
    ELSE
      convResult := "";
    ENDIF;
  END;

BEGIN
  Call AddProc(3,7);
  ASSERT addResult = 10;
  Call ConvProc(addResult);
  ASSERT convResult = "10";
  outputVar := convResult;
  ASSERT outputVar = "10";
END; --algorithm

Spec == Init /\ [][Next]_<<pc, addResult, convResult, outputVar>>

Liveness == <> (pc = "Done")