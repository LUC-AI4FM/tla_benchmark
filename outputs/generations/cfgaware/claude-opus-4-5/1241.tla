---------------------------- MODULE GlobalNamingPlusCal ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Object, Any

(***************************************************************************)
(* This module specifies the translation from the abstract syntax tree    *)
(* of a global-naming PlusCal (+CAL) algorithm into a TLA+ specification. *)
(***************************************************************************)

(***************************************************************************)
(* Fairness options for generated specifications                          *)
(***************************************************************************)
NoFairness == "none"
WeakFairnessOfProcessActions == "wf_process"
WeakFairnessOfNext == "wf_next"
StrongFairnessOfProcessActions == "sf_process"

FairnessOptions == {NoFairness, WeakFairnessOfProcessActions, 
                    WeakFairnessOfNext, StrongFairnessOfProcessActions}

(***************************************************************************)
(* Lexeme representation - sequences of strings representing TLA+ output  *)
(***************************************************************************)
Lexeme == Seq(STRING)

(***************************************************************************)
(* AST Node Types for PlusCal grammar                                     *)
(***************************************************************************)
NodeTypes == {"Algorithm", "Procedure", "Process", "LabeledStmt", 
              "Variable", "Assignment", "If", "While", "Either",
              "With", "Call", "Return", "Goto", "Print", "Assert",
              "Skip", "Await", "MacroCall", "Expression"}

(***************************************************************************)
(* Abstract Syntax Tree representation                                     *)
(* An AST node is a record with at least a "type" field                   *)
(***************************************************************************)
ASTNode == [type : NodeTypes] \cup Object

(***************************************************************************)
(* Check if something is a valid AST node                                 *)
(***************************************************************************)
IsASTNode(node) == 
    /\ node \in Object \/ node = Any
    /\ \/ node = Any
       \/ /\ "type" \in DOMAIN node
          /\ node.type \in NodeTypes

(***************************************************************************)
(* Grammar predicates for legal abstract syntax trees                     *)
(***************************************************************************)

(* Variable declaration *)
IsVariable(v) ==
    \/ v = Any
    \/ /\ "type" \in DOMAIN v
       /\ v.type = "Variable"
       /\ "name" \in DOMAIN v
       /\ "init" \in DOMAIN v

(* Expression *)
IsExpression(e) ==
    \/ e = Any
    \/ /\ "type" \in DOMAIN e
       /\ e.type = "Expression"

(* Statement types *)
IsStatement(s) ==
    \/ s = Any
    \/ /\ "type" \in DOMAIN s
       /\ s.type \in {"Assignment", "If", "While", "Either", "With",
                      "Call", "Return", "Goto", "Print", "Assert",
                      "Skip", "Await", "MacroCall"}

(* Labeled statement: a label followed by a sequence of statements *)
IsLabeledStmt(ls) ==
    \/ ls = Any
    \/ /\ "type" \in DOMAIN ls
       /\ ls.type = "LabeledStmt"
       /\ "label" \in DOMAIN ls
       /\ "stmts" \in DOMAIN ls

(* Procedure definition *)
IsProcedure(p) ==
    \/ p = Any
    \/ /\ "type" \in DOMAIN p
       /\ p.type = "Procedure"
       /\ "name" \in DOMAIN p
       /\ "params" \in DOMAIN p
       /\ "vars" \in DOMAIN p
       /\ "body" \in DOMAIN p

(* Process definition *)
IsProcess(p) ==
    \/ p = Any
    \/ /\ "type" \in DOMAIN p
       /\ p.type = "Process"
       /\ "name" \in DOMAIN p
       /\ "id" \in DOMAIN p
       /\ "vars" \in DOMAIN p
       /\ "body" \in DOMAIN p

(* Algorithm - the top-level AST *)
IsAlgorithm(a) ==
    \/ a = Any
    \/ /\ "type" \in DOMAIN a
       /\ a.type = "Algorithm"
       /\ "name" \in DOMAIN a
       /\ "vars" \in DOMAIN a
       /\ "procedures" \in DOMAIN a
       /\ "processes" \in DOMAIN a

(***************************************************************************)
(* Translation operators - convert AST nodes to lexeme sequences          *)
(***************************************************************************)

(* Translate a variable declaration *)
TranslateVariable(v) ==
    IF v = Any THEN <<"ANY_VAR">>
    ELSE <<v.name, " = ", "InitValue">>

(* Translate an expression *)
TranslateExpression(e) ==
    IF e = Any THEN <<"ANY_EXPR">>
    ELSE <<"expr">>

(* Translate a labeled statement *)
TranslateLabeledStmt(ls) ==
    IF ls = Any THEN <<"ANY_LABELED_STMT">>
    ELSE <<ls.label, ":">>

(* Translate a procedure *)
TranslateProcedure(p) ==
    IF p = Any THEN <<"ANY_PROCEDURE">>
    ELSE <<"procedure ", p.name>>

(* Translate a process *)
TranslateProcess(p) ==
    IF p = Any THEN <<"ANY_PROCESS">>
    ELSE <<"process ", p.name>>

(***************************************************************************)
(* Generate Init predicate                                                 *)
(***************************************************************************)
GenerateInit(alg) ==
    IF alg = Any THEN <<"Init == TRUE">>
    ELSE <<"Init == ", "/\\ pc = \"start\"">>

(***************************************************************************)
(* Generate Next predicate                                                 *)
(***************************************************************************)
GenerateNext(alg) ==
    IF alg = Any THEN <<"Next == TRUE">>
    ELSE <<"Next == ", "\\/ Step">>

(***************************************************************************)
(* Generate Spec with fairness                                             *)
(***************************************************************************)
GenerateSpec(alg, fairness) ==
    LET base == <<"Spec == Init /\\ [][Next]_vars">>
    IN IF fairness = NoFairness THEN base
       ELSE IF fairness = WeakFairnessOfNext THEN 
            <<"Spec == Init /\\ [][Next]_vars /\\ WF_vars(Next)">>
       ELSE IF fairness = WeakFairnessOfProcessActions THEN
            <<"Spec == Init /\\ [][Next]_vars /\\ WF_vars(ProcessAction)">>
       ELSE IF fairness = StrongFairnessOfProcessActions THEN
            <<"Spec == Init /\\ [][Next]_vars /\\ SF_vars(ProcessAction)">>
       ELSE base

(***************************************************************************)
(* Generate Termination property                                           *)
(***************************************************************************)
GenerateTermination(alg) ==
    <<"Termination == <>(pc = \"Done\")">>

(***************************************************************************)
(* Main translation operator                                               *)
(***************************************************************************)
Translate(alg, fairness) ==
    IF ~IsAlgorithm(alg) THEN <<"ERROR: Invalid algorithm AST">>
    ELSE IF ~(fairness \in FairnessOptions) THEN <<"ERROR: Invalid fairness">>
    ELSE GenerateInit(alg) \o GenerateNext(alg) \o 
         GenerateSpec(alg, fairness) \o GenerateTermination(alg)

(***************************************************************************)
(* Error handling - representation hacks and limitations noted here       *)
(* - Some complex expressions may not translate correctly                  *)
(* - Formatting of output is simplified                                    *)
(* - Macro expansion has limitations                                       *)
(***************************************************************************)
TranslationError(msg) == <<"ERROR: ", msg>>

(***************************************************************************)
(* Utility operators                                                       *)
(***************************************************************************)
ConcatLexemes(l1, l2) == l1 \o l2

EmptyLexeme == <<>>

=============================================================================