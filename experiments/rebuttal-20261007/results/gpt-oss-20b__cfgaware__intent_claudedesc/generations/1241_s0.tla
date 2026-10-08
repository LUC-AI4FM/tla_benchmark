------------------------------ MODULE PlusCalTranslation ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Object, Any

-- Types
Name == String

Stmt ==
  [type : Name] \* base type; actual fields depend on the value of 'type'

Assignment == [type : "assign", var : Name, expr : Exp]
Call       == [type : "call",   proc : Name, args : Seq(Exp)]
Return     == [type : "return"]
Goto       == [type : "goto",   label : Name]
LabelStmt  == [type : "label",  name : Name]
WhileStmt  == [type : "while",  cond : Exp, body : Seq(Stmt)]
IfStmt     == [type : "if",     cond : Exp, thenBody : Seq(Stmt), elseBody : Seq(Stmt)]
EitherStmt == [type : "either", cases : Seq([cond : Exp, body : Seq(Stmt)])]
WithStmt   == [type : "with",   vars : Seq(Name), body : Seq(Stmt)]
WhenStmt   == [type : "when",   cond : Exp, body : Seq(Stmt)]
PrintStmt  == [type : "print",  exprs : Seq(Exp)]
AssertStmt == [type : "assert", cond : Exp]
SkipStmt   == [type : "skip"]

-- Expression type placeholder
Exp == Any

-- Procedure definition
Procedure ==
  [name : Name, params : Seq(Name), body : Seq(Stmt)]

-- Process definition (for multiprocess algorithms)
Process ==
  [id : Nat, vars : Seq(Name), body : Seq(Stmt)]

-- Algorithm type
Alg ==
  [kind : Name, content : Any]

PROC_ALG      == "proc"
MULTI_PROC_ALG== "multi"

-- Fairness options
NO_FAIRNESS   == "no"
WEAK_ALL      == "weak_all"
WEAK_NEXT     == "weak_next"
STRONG_ALL    == "strong_all"

FairnessOption == {NO_FAIRNESS, WEAK_ALL, WEAK_NEXT, STRONG_ALL}

-- Translation operator
Translation(alg, fairnessOption) ==
  LET
    initLines        == ["Init := ..."]
    nextLines        == ["Next := ..."]
    procSetLines     == ["ProcSet := ..."]
    terminationLines == ["Termination == ..."]

    fairnessLines ==
      CASE fairnessOption = NO_FAIRNESS -> []
           fairnessOption = WEAK_ALL  -> ["-- Weak fairness of all process actions"]
           fairnessOption = WEAK_NEXT -> ["-- Weak fairness of entire Next action"]
           fairnessOption = STRONG_ALL-> ["-- Strong fairness of all process actions"]

    algLines ==
      CASE alg.kind = PROC_ALG ->
        ["-- Translating single-process algorithm: " \o alg.content.name]
      [] alg.kind = MULTI_PROC_ALG ->
        ["-- Translating multi-process algorithm with processes"]
  IN
    fairnessLines \o initLines \o nextLines \o procSetLines \o terminationLines \o algLines

=============================================================================