MODULE OldPlusCal
EXTENDS Sequences, TLC

CONSTANTS
    Object,
    Any

(* ------------------------------------------------------------------ *)
(*  AST Kinds                                                        *)
(* ------------------------------------------------------------------ *)

AlgorithmKind   == {"algorithm"}
ProcedureKind   == {"procedure"}
ProcessKind     == {"process"}
VariableDeclKind== {"varDecl"}
LabeledStmtKind == {"labeledStmt"}
WhileLoopKind   == {"while"}
LabelSeqKind    == {"labelSeq"}
SimpleStmtKind  == {"assignment", "if", "either", "with", "when", "print", "assert", "skip"}
CallReturnKind  == {"call", "return", "callReturn"}
GotoKind        == {"goto"}

(* ------------------------------------------------------------------ *)
(*  Predicates for AST nodes                                         *)
(* ------------------------------------------------------------------ *)

IsAlgorithm(alg) ==
    /\ alg?kind
    /\ alg.kind \in AlgorithmKind

IsProcedure(proc) ==
    /\ proc?kind
    /\ proc.kind \in ProcedureKind

IsProcess(proc) ==
    /\ proc?kind
    /\ proc.kind \in ProcessKind

IsVariableDecl(vd) ==
    /\ vd?kind
    /\ vd.kind \in VariableDeclKind

IsLabeledStmt(ls) ==
    /\ ls?kind
    /\ ls.kind \in LabeledStmtKind

IsWhileLoop(wh) ==
    /\ wh?kind
    /\ wh.kind \in WhileLoopKind

IsLabelSeq(lsq) ==
    /\ lsq?kind
    /\ lsq.kind \in LabelSeqKind

IsSimpleStmt(ss) ==
    /\ ss?kind
    /\ ss.kind \in SimpleStmtKind

IsCallReturn(cr) ==
    /\ cr?kind
    /\ cr.kind \in CallReturnKind

IsGoto(g) ==
    /\ g?kind
    /\ g.kind = "goto"

(* ------------------------------------------------------------------ *)
(*  Explode a single statement into a sequence of lexemes           *)
(* ------------------------------------------------------------------ *)

Explode(stmt) ==
    CASE stmt.kind = "assignment" ->
            [ "\t" + stmt.lhs + " := " + stmt.rhs ]
         stmt.kind = "if" ->
            [ "\tIF " + stmt.condition + " THEN",
              "\tEND IF" ]  (* simplified representation *)
         stmt.kind = "skip" ->
            [ "\tSKIP" ]
         TRUE -> []

(* ------------------------------------------------------------------ *)
(*  Fully explode the body of an algorithm into a TLA+ module        *)
(* ------------------------------------------------------------------ *)

FullyExplodeSeq(alg) ==
    IF IsAlgorithm(alg)
        THEN
            LET header == ["MODULE " + alg.name]
                bodySeq == SeqConcat([ Explode(s) : s \in alg.body ])
                footer == ["END MODULE"]
            IN
                header ++ bodySeq ++ footer
        ELSE
            []

(* ------------------------------------------------------------------ *)
(*  Translation operator                                               *)
(* ------------------------------------------------------------------ *)

Translation(alg, fairnessOption) ==
    LET seq == FullyExplodeSeq(alg)
        fairnessSeq ==
            IF fairnessOption = "" THEN []
            ELSE IF fairnessOption = "wf" THEN ["WF"]
            ELSE IF fairnessOption = "wfNext" THEN ["WF_NEXT"]
            ELSE IF fairnessOption = "sf" THEN ["SF"]
            ELSE []
    IN
        seq ++ fairnessSeq

(* ------------------------------------------------------------------ *)
(*  Show translation when TLC runs                                    *)
(* ------------------------------------------------------------------ *)

ShowTranslation ==
    LET _ == Print(Translation(Object, Any)) IN TRUE

ASSUME ShowTranslation

END MODULE