------------------------------ MODULE XPlusCal ------------------------------
EXTENDS Naturals

CONSTANTS Object, Any, Ast, FairnessOption

(* --- Operator definitions (placeholders) --- *)

Explode(stmt) == <<stmt>>

FullyExplodeSeq(seq) == seq

XlateCall(call) == <<call>>

XlateReturn(ret) == <<ret>>

XlateCallReturn(cr) == <<cr>>

XlateGoto(goto) == <<goto>>

AddSubscript(var) == <<var>>

ProcessVars(proc) == <<proc>>

Init == TRUE

Next == FALSE

Spec == Init /\ []Next

Termination == <>FALSE

Translation(alg, fairnessOption) ==
  LET
    ExplodeLocal          == [stmt |-> stmt]
    FullyExplodeSeqLocal   == [seq |-> seq]
    XlateCallLocal        == [call |-> call]
    XlateReturnLocal      == [ret |-> ret]
    XlateCallReturnLocal  == [cr |-> cr]
    XlateGotoLocal        == [goto |-> goto]
    AddSubscriptLocal     == [var |-> var]
    ProcessVarsLocal      == [proc |-> proc]
  IN
    <<>>   (* placeholder for the full TLA+ specification string *)

ASSUME
  Translation(Ast, FairnessOption) = <<>>

=============================================================================