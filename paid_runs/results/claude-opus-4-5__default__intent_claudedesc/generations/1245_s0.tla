---------------------------- MODULE PCalTranslator ----------------------------
(***************************************************************************)
(* TLA+ specification for translating +CAL AST to TLA+ lexemes             *)
(***************************************************************************)

EXTENDS Sequences, Naturals, FiniteSets, TLC

CONSTANTS
    \* Identifiers and literals
    Identifiers,        \* Set of valid identifier names
    Literals,           \* Set of literal values (numbers, strings)
    
    \* Fairness options
    NoFairness,
    WeakFairnessPerAction,
    WeakFairnessWhole,
    StrongFairnessPerAction

ASSUME NoFairness \in Identifiers
ASSUME WeakFairnessPerAction \in Identifiers
ASSUME WeakFairnessWhole \in Identifiers
ASSUME StrongFairnessPerAction \in Identifiers

(***************************************************************************)
(* Lexeme Types for TLA+ output                                            *)
(***************************************************************************)

LexemeTypes == {
    "IDENT", "LITERAL", "KEYWORD", "OPERATOR", "PUNCTUATION", "NEWLINE", "INDENT"
}

Lexeme == [type: LexemeTypes, value: Seq(Identifiers) \cup Identifiers \cup Literals \cup {""}]

(***************************************************************************)
(* +CAL Expression Grammar                                                  *)
(***************************************************************************)

RECURSIVE IsExpr(_)
RECURSIVE IsExprSeq(_)

\* Expressions are represented as records
IsExpr(e) ==
    \/ /\ e.tag = "Ident"
       /\ e.name \in Identifiers
    \/ /\ e.tag = "Literal"
       /\ e.value \in Literals
    \/ /\ e.tag = "BinOp"
       /\ e.op \in {"+", "-", "*", "/", "\\div", "\\mod", "=", "#", "<", ">", "<=", ">=", 
                    "/\\", "\\/", "=>", "<=>", "\\in", "\\notin", "\\union", "\\intersect", "\\subseteq"}
       /\ IsExpr(e.left)
       /\ IsExpr(e.right)
    \/ /\ e.tag = "UnaryOp"
       /\ e.op \in {"~", "-", "DOMAIN", "SUBSET", "UNION"}
       /\ IsExpr(e.operand)
    \/ /\ e.tag = "FuncApp"
       /\ IsExpr(e.func)
       /\ IsExprSeq(e.args)
    \/ /\ e.tag = "RecordField"
       /\ IsExpr(e.record)
       /\ e.field \in Identifiers
    \/ /\ e.tag = "SetEnum"
       /\ IsExprSeq(e.elements)
    \/ /\ e.tag = "SeqEnum"
       /\ IsExprSeq(e.elements)
    \/ /\ e.tag = "RecordCons"
       /\ \A i \in DOMAIN e.fields: 
          /\ e.fields[i].name \in Identifiers
          /\ IsExpr(e.fields[i].value)
    \/ /\ e.tag = "IfThenElse"
       /\ IsExpr(e.cond)
       /\ IsExpr(e.thenExpr)
       /\ IsExpr(e.elseExpr)
    \/ /\ e.tag = "QuantExpr"
       /\ e.quant \in {"\\A", "\\E"}
       /\ e.boundVar \in Identifiers
       /\ IsExpr(e.domain)
       /\ IsExpr(e.body)
    \/ /\ e.tag = "EXCEPT"
       /\ IsExpr(e.base)
       /\ \A i \in DOMAIN e.updates:
          /\ IsExprSeq(e.updates[i].path)
          /\ IsExpr(e.updates[i].value)
    \/ /\ e.tag = "Prime"
       /\ IsExpr(e.expr)

IsExprSeq(es) ==
    /\ es \in Seq([tag: {"Ident", "Literal", "BinOp", "UnaryOp", "FuncApp", 
                         "RecordField", "SetEnum", "SeqEnum", "RecordCons",
                         "IfThenElse", "QuantExpr", "EXCEPT", "Prime"}])
    /\ \A i \in DOMAIN es: IsExpr(es[i])

(***************************************************************************)
(* +CAL Variable Declaration Grammar                                        *)
(***************************************************************************)

IsVarDecl(v) ==
    /\ v.name \in Identifiers
    /\ \/ v.initType = "none"
       \/ /\ v.initType = "value"
          /\ IsExpr(v.initValue)
       \/ /\ v.initType = "in"
          /\ IsExpr(v.initSet)

IsVarDeclSeq(vs) ==
    /\ vs \in Seq([name: Identifiers, initType: {"none", "value", "in"}])
    /\ \A i \in DOMAIN vs: IsVarDecl(vs[i])

(***************************************************************************)
(* +CAL Statement Grammar                                                   *)
(***************************************************************************)

RECURSIVE IsStmt(_)
RECURSIVE IsStmtSeq(_)
RECURSIVE IsLabeledStmtSeq(_)

\* Simple statements
IsAssignment(s) ==
    /\ s.tag = "Assign"
    /\ \A i \in DOMAIN s.assignments:
       /\ s.assignments[i].lhs.var \in Identifiers
       /\ \/ s.assignments[i].lhs.indices = <<>>
          \/ IsExprSeq(s.assignments[i].lhs.indices)
       /\ IsExpr(s.assignments[i].rhs)

IsWhen(s) ==
    /\ s.tag = "When"
    /\ IsExpr(s.cond)

IsPrint(s) ==
    /\ s.tag = "Print"
    /\ IsExpr(s.expr)

IsAssert(s) ==
    /\ s.tag = "Assert"
    /\ IsExpr(s.expr)

IsSkip(s) ==
    s.tag = "Skip"

IsCall(s) ==
    /\ s.tag = "Call"
    /\ s.proc \in Identifiers
    /\ IsExprSeq(s.args)

IsReturn(s) ==
    s.tag = "Return"

IsCallReturn(s) ==
    /\ s.tag = "CallReturn"
    /\ s.proc \in Identifiers
    /\ IsExprSeq(s.args)

IsGoto(s) ==
    /\ s.tag = "Goto"
    /\ s.label \in Identifiers

\* Compound statements
IsIf(s) ==
    /\ s.tag = "If"
    /\ IsExpr(s.cond)
    /\ IsStmtSeq(s.thenBranch)
    /\ \/ s.elseBranch = <<>>
       \/ IsStmtSeq(s.elseBranch)

IsEither(s) ==
    /\ s.tag = "Either"
    /\ \A i \in DOMAIN s.branches: IsStmtSeq(s.branches[i])

IsWith(s) ==
    /\ s.tag = "With"
    /\ s.var \in Identifiers
    /\ \/ /\ s.bindType = "in"
          /\ IsExpr(s.set)
       \/ /\ s.bindType = "eq"
          /\ IsExpr(s.value)
    /\ IsStmtSeq(s.body)

IsWhile(s) ==
    /\ s.tag = "While"
    /\ IsExpr(s.cond)
    /\ IsLabeledStmtSeq(s.body)

IsStmt(s) ==
    \/ IsAssignment(s)
    \/ IsWhen(s)
    \/ IsPrint(s)
    \/ IsAssert(s)
    \/ IsSkip(s)
    \/ IsCall(s)
    \/ IsReturn(s)
    \/ IsCallReturn(s)
    \/ IsGoto(s)
    \/ IsIf(s)
    \/ IsEither(s)
    \/ IsWith(s)
    \/ IsWhile(s)

IsStmtSeq(ss) ==
    /\ ss \in Seq([tag: {"Assign", "When", "Print", "Assert", "Skip", 
                         "Call", "Return", "CallReturn", "Goto",
                         "If", "Either", "With", "While"}])
    /\ \A i \in DOMAIN ss: IsStmt(ss[i])

\* Labeled statement
IsLabeledStmt(ls) ==
    /\ ls.label \in Identifiers
    /\ ls.labelType \in {"none", "plus", "minus"}  \* fairness annotations
    /\ IsStmtSeq(ls.stmts)

IsLabeledStmtSeq(lss) ==
    /\ lss \in Seq([label: Identifiers, labelType: {"none", "plus", "minus"}])
    /\ \A i \in DOMAIN lss: IsLabeledStmt(lss[i])

(***************************************************************************)
(* +CAL Procedure Grammar                                                   *)
(***************************************************************************)

IsProcedure(p) ==
    /\ p.name \in Identifiers
    /\ IsVarDeclSeq(p.params)
    /\ IsVarDeclSeq(p.localVars)
    /\ IsLabeledStmtSeq(p.body)

IsProcedureSeq(ps) ==
    \A i \in DOMAIN ps: IsProcedure(ps[i])

(***************************************************************************)
(* +CAL Process Grammar (for multiprocess algorithms)                       *)
(***************************************************************************)

IsProcess(pr) ==
    /\ pr.name \in Identifiers
    /\ pr.idType \in {"eq", "in"}  \* single process vs process set
    /\ IsExpr(pr.idExpr)
    /\ IsVarDeclSeq(pr.localVars)
    /\ IsLabeledStmtSeq(pr.body)

IsProcessSeq(prs) ==
    \A i \in DOMAIN prs: IsProcess(prs[i])

(***************************************************************************)
(* +CAL Algorithm AST Grammar                                               *)
(***************************************************************************)

IsAlgorithmAST(ast) ==
    /\ ast.name \in Identifiers
    /\ IsVarDeclSeq(ast.globalVars)
    /\ IsProcedureSeq(ast.procedures)
    /\ \/ /\ ast.algType = "uniprocess"
          /\ IsLabeledStmtSeq(ast.body)
       \/ /\ ast.algType = "multiprocess"
          /\ IsProcessSeq(ast.processes)

(***************************************************************************)
(* Helper: Lexeme Construction                                              *)
(***************************************************************************)

MkIdent(name) == [type |-> "IDENT", value |-> name]
MkLiteral(val) == [type |-> "LITERAL", value |-> val]
MkKeyword(kw) == [type |-> "KEYWORD", value |-> kw]
MkOp(op) == [type |-> "OPERATOR", value |-> op]
MkPunct(p) == [type |-> "PUNCTUATION", value |-> p]
MkNewline == [type |-> "NEWLINE", value |-> ""]
MkIndent(n) == [type |-> "INDENT", value |-> n]

(***************************************************************************)
(* Translation: Expression to Lexemes                                       *)
(***************************************************************************)

RECURSIVE TranslateExpr(_, _)
RECURSIVE TranslateExprSeq(_, _, _)

TranslateExpr(e, self) ==
    CASE e.tag = "Ident" ->
         IF self = "none"
         THEN <<MkIdent(e.name)>>
         ELSE <<MkIdent(e.name), MkPunct("["), MkIdent(self), MkPunct("]")>>
         
    [] e.tag = "Literal" ->
         <<MkLiteral(e.value)>>
         
    [] e.tag = "BinOp" ->
         <<MkPunct("(")>> \o TranslateExpr(e.left, self) \o 
         <<MkOp(e.op)>> \o TranslateExpr(e.right, self) \o <<MkPunct(")")>>
         
    [] e.tag = "UnaryOp" ->
         <<MkOp(e.op)>> \o TranslateExpr(e.operand, self)
         
    [] e.tag = "FuncApp" ->
         TranslateExpr(e.func, self) \o <<MkPunct("[")>> \o
         TranslateExprSeq(e.args, self, ",") \o <<MkPunct("]")>>
         
    [] e.tag = "RecordField" ->
         TranslateExpr(e.record, self) \o <<MkPunct("."), MkIdent(e.field)>>
         
    [] e.tag = "SetEnum" ->
         <<MkPunct("{")>> \o TranslateExprSeq(e.elements, self, ",") \o <<MkPunct("}")>>
         
    [] e.tag = "SeqEnum" ->
         <<MkPunct("<<")>> \o TranslateExprSeq(e.elements, self, ",") \o <<MkPunct(">>")>>
         
    [] e.tag = "IfThenElse" ->
         <<MkKeyword("IF")>> \o TranslateExpr(e.cond, self) \o
         <<MkKeyword("THEN")>> \o TranslateExpr(e.thenExpr, self) \o
         <<MkKeyword("ELSE")>> \o TranslateExpr(e.elseExpr, self)
         
    [] e.tag = "QuantExpr" ->
         <<MkOp(e.quant), MkIdent(e.boundVar), MkOp("\\in")>> \o
         TranslateExpr(e.domain, self) \o <<MkPunct(":")>> \o
         TranslateExpr(e.body, self)
         
    [] e.tag = "Prime" ->
         TranslateExpr(e.expr, self) \o <<MkOp("'")>>
         
    [] OTHER -> <<>>

TranslateExprSeq(es, self, sep) ==
    IF es = <<>> THEN <<>>
    ELSE IF Len(es) = 1 THEN TranslateExpr(es[1], self)
    ELSE TranslateExpr(es[1], self) \o <<MkPunct(sep)>> \o 
         TranslateExprSeq(Tail(es), self, sep)

(***************************************************************************)
(* Translation: Variable Declarations                                       *)
(***************************************************************************)

TranslateVarDecl(v, self) ==
    LET base == IF self = "none" THEN <<MkIdent(v.name)>>
                ELSE <<MkIdent(v.name), MkPunct("["), MkIdent(self), MkPunct("]")>>
    IN CASE v.initType = "none" -> base
       [] v.initType = "value" -> 
          base \o <<MkOp("=")>> \o TranslateExpr(v.initValue, self)
       [] v.initType = "in" ->
          base \o <<MkOp("\\in")>> \o TranslateExpr(v.initSet, self)

RECURSIVE TranslateVarDeclSeq(_, _)
TranslateVarDeclSeq(vs, self) ==
    IF vs = <<>> THEN <<>>
    ELSE IF Len(vs) = 1 THEN TranslateVarDecl(vs[1], self)
    ELSE TranslateVarDecl(vs[1], self) \o <<MkPunct(","), MkNewline>> \o
         TranslateVarDeclSeq(Tail(vs), self)

(***************************************************************************)
(* Translation: Init Predicate                                              *)
(***************************************************************************)

TranslateVarInit(v, self) ==
    LET varRef == IF self = "none" THEN <<MkIdent(v.name)>>
                  ELSE <<MkIdent(v.name), MkPunct("["), MkIdent(self), MkPunct("]")>>
    IN CASE v.initType = "none" -> <<>>
       [] v.initType = "value" ->
          varRef \o <<MkOp("=")>> \o TranslateExpr(v.initValue, self)
       [] v.initType = "in" ->
          varRef \o <<MkOp("\\in")>> \o TranslateExpr(v.initSet, self)

RECURSIVE TranslateVarInitSeq(_, _)
TranslateVarInitSeq(vs, self) ==
    IF vs = <<>> THEN <<>>
    ELSE LET first == TranslateVarInit(vs[1], self)
         IN IF first = <<>> THEN TranslateVarInitSeq(Tail(vs), self)
            ELSE IF Len(vs) = 1 THEN first
            ELSE first \o <<MkOp("/\\"), MkNewline>> \o TranslateVarInitSeq(Tail(vs), self)

(***************************************************************************)
(* Translation: Statement to Action                                         *)
(***************************************************************************)

RECURSIVE TranslateStmt(_, _, _, _)
RECURSIVE TranslateStmtSeq(_, _, _, _)

\* Get all labels from a labeled statement sequence
RECURSIVE GetLabels(_)
GetLabels(lss) ==
    IF lss = <<>> THEN {}
    ELSE {lss[1].label} \cup GetLabels(Tail(lss))

\* nextLabel is the label to jump to after this statement (or "Done")
TranslateStmt(s, self, nextLabel, procName) ==
    CASE s.tag = "Assign" ->
         LET TranslateOneAssign(a) ==
             LET lhs == IF a.lhs.indices = <<>>
                       THEN IF self = "none" THEN <<MkIdent(a.lhs.var), MkOp("'")>>
                            ELSE <<MkIdent(a.lhs.var), MkOp("'"), MkPunct("["), MkIdent(self), MkPunct("]")>>
                       ELSE IF self = "none" 
                            THEN <<MkIdent(a.lhs.var), MkOp("'")>> \o 
                                 <<MkPunct("[")>> \o TranslateExprSeq(a.lhs.indices, self, ",") \o <<MkPunct("]")>>
                            ELSE <<MkIdent(a.lhs.var), MkOp("'"), MkPunct("["), MkIdent(self), MkPunct("]")>> \o
                                 <<MkPunct("[")>> \o TranslateExprSeq(a.lhs.indices, self, ",") \o <<MkPunct("]")>>
             IN lhs \o <<MkOp("=")>> \o TranslateExpr(a.rhs, self)
         IN IF Len(s.assignments) = 1 
            THEN TranslateOneAssign(s.assignments[1])
            ELSE <<MkOp("/\\")>> \o TranslateOneAssign(s.assignments[1]) \o
                 <<MkNewline, MkOp("/\\")>> \o TranslateOneAssign(s.assignments[2])
                 
    [] s.tag = "When" ->
         TranslateExpr(s.cond, self)
         
    [] s.tag = "Print" ->
         <<MkIdent("PrintT"), MkPunct("(")>> \o TranslateExpr(s.expr, self) \o <<MkPunct(")")>>
         
    [] s.tag = "Assert" ->
         <<MkIdent("Assert"), MkPunct("(")>> \o TranslateExpr(s.expr, self) \o <<MkPunct(")")>>
         
    [] s.tag = "Skip" ->
         <<MkKeyword("TRUE")>>
         
    [] s.tag = "Call" ->
         \* Push current state to stack, set pc to procedure entry
         LET stackPush == 
             IF self = "none"
             THEN <<MkIdent("stack"), MkOp("'"), MkOp("="), 
                    MkPunct("<<"), MkPunct("["),
                    MkIdent("procedure"), MkOp("|->"), MkLiteral(s.proc), MkPunct(","),
                    MkIdent("pc"), MkOp("|->"), MkLiteral(nextLabel),
                    MkPunct("]"), MkPunct(">>"), MkOp("\\o"), MkIdent("stack")>>
             ELSE <<MkIdent("stack"), MkOp("'"), MkPunct("["), MkIdent(self), MkPunct("]"), MkOp("="),
                    MkPunct("<<"), MkPunct("["),
                    MkIdent("procedure"), MkOp("|->"), MkLiteral(s.proc), MkPunct(","),
                    MkIdent("pc"), MkOp("|->"), MkLiteral(nextLabel),
                    MkPunct("]"), MkPunct(">>"), MkOp("\\o"), MkIdent("stack"), 
                    MkPunct("["), MkIdent(self), MkPunct("]")>>
         IN stackPush
         
    [] s.tag = "Return" ->
         \* Pop from stack, restore pc
         IF self = "none"
         THEN <<MkIdent("pc"), MkOp("'"), MkOp("="), 
                MkIdent("Head"), MkPunct("("), MkIdent("stack"), MkPunct(")"), MkPunct("."), MkIdent("pc"),
                MkOp("/\\"),
                MkIdent("stack"), MkOp("'"), MkOp("="), 
                MkIdent("Tail"), MkPunct("("), MkIdent("stack"), MkPunct(")")>>
         ELSE <<MkIdent("pc"), MkOp("'"), MkPunct("["), MkIdent(self), MkPunct("]"), MkOp("="),
                MkIdent("Head"), MkPunct("("), MkIdent("stack"), MkPunct("["), MkIdent(self), MkPunct("]"), MkPunct(")"), MkPunct("."), MkIdent("pc"),
                MkOp("/\\"),
                MkIdent("stack"), MkOp("'"), MkPunct("["), MkIdent(self), MkPunct("]"), MkOp("="),
                MkIdent("Tail"), MkPunct("("), MkIdent("stack"), MkPunct("["), MkIdent(self), MkPunct("]"), MkPunct(")")>>
                
    [] s.tag = "CallReturn" ->
         \* Combined: don't push, just jump to procedure (tail call)
         IF self = "none"
         THEN <<MkIdent("pc"), MkOp("'"), MkOp("="), MkLiteral(s.proc)>>
         ELSE <<MkIdent("pc"), MkOp("'"), MkPunct("["), MkIdent(self), MkPunct("]"), MkOp("="), MkLiteral(s.proc)>>
         
    [] s.tag = "Goto" ->
         IF self = "none"
         THEN <<MkIdent("pc"), MkOp("'"), MkOp("="), MkLiteral(s.label)>>
         ELSE <<MkIdent("pc"), MkOp("'"), MkPunct("["), MkIdent(self), MkPunct("]"), MkOp("="), MkLiteral(s.label)>>
         
    [] s.tag = "If" ->
         <<MkOp("\\/"), MkPunct("(")>> \o TranslateExpr(s.cond, self) \o 
         <<MkOp("/\\")>> \o TranslateStmtSeq(s.thenBranch, self, nextLabel, procName) \o <<MkPunct(")")>> \o
         <<MkNewline, MkOp("\\/"), MkPunct("("), MkOp("~"), MkPunct("(")>> \o 
         TranslateExpr(s.cond, self) \o <<MkPunct(")")>> \o
         <<MkOp("/\\")>> \o 
         (IF s.elseBranch = <<>> 
          THEN <<MkKeyword("TRUE")>>
          ELSE TranslateStmtSeq(s.elseBranch, self, nextLabel, procName)) \o 
         <<MkPunct(")")>>
         
    [] s.tag = "Either" ->
         <<MkOp("\\/")>> \o TranslateStmtSeq(s.branches[1], self, nextLabel, procName)
         
    [] s.tag = "With" ->
         <<MkOp("\\E"), MkIdent(s.var)>> \o
         (IF s.bindType = "in" 
          THEN <<MkOp("\\in")>> \o TranslateExpr(s.set, self)
          ELSE <<MkOp("=")>> \o TranslateExpr(s.value, self)) \o
         <<MkPunct(":")>> \o TranslateStmtSeq(s.body, self, nextLabel, procName)
         
    [] s.tag = "While" ->
         \* While is handled at labeled statement level
         <<>>
         
    [] OTHER -> <<>>

TranslateStmtSeq(ss, self, nextLabel, procName) ==
    IF ss = <<>> THEN <<MkKeyword("TRUE")>>
    ELSE IF Len(ss) = 1 THEN TranslateStmt(ss[1], self, nextLabel, procName)
    ELSE TranslateStmt(ss[1], self, nextLabel, procName) \o 
         <<MkOp("/\\"), MkNewline>> \o 
         TranslateStmtSeq(Tail(ss), self, nextLabel, procName)

(***************************************************************************)
(* Translation: Labeled Statement to Action Definition                      *)
(***************************************************************************)

TranslateLabeledStmt(ls, self, nextLabel, procName, allVars) ==
    LET actionName == ls.label
        pcGuard == IF self = "none"
                   THEN <<MkIdent("pc"), MkOp("="), MkLiteral(ls.label)>>
                   ELSE <<MkIdent("pc"), MkPunct("["), MkIdent(self), MkPunct("]"), 
                          MkOp("="), MkLiteral(ls.label)>>
        pcUpdate == IF self = "none"
                    THEN <<MkIdent("pc"), MkOp("'"), MkOp("="), MkLiteral(nextLabel)>>
                    ELSE <<MkIdent("pc"), MkOp("'"), MkPunct("["), MkIdent(self), MkPunct("]"),
                           MkOp("="), MkLiteral(nextLabel)>>
        body == TranslateStmtSeq(ls.stmts, self, nextLabel, procName)
        unchangedClause == <<MkKeyword("UNCHANGED"), MkPunct("<<")>> \o
                          (IF allVars = <<>> THEN <<>>
                           ELSE <<MkIdent(allVars[1])>>) \o
                          <<MkPunct(">>")>>
    IN <<MkIdent(actionName)>> \o
       (IF self # "none" THEN <<MkPunct("("), MkIdent(self), MkPunct(")")>> ELSE <<>>) \o
       <<MkOp("=="), MkNewline, MkIndent(2)>> \o
       pcGuard \o <<MkNewline, MkOp("/\\")>> \o
       body \o <<MkNewline, MkOp("/\\")>> \o
       pcUpdate

(***************************************************************************)
(* Translation: Full Algorithm                                              *)
(***************************************************************************)

\* Collect all variable names from algorithm
RECURSIVE CollectVarNames(_)
CollectVarNames(vs) ==
    IF vs = <<>> THEN {}
    ELSE {vs[1].name} \cup CollectVarNames(Tail(vs))

\* Collect all labels from algorithm
RECURSIVE CollectLabelsFromLSS(_)
CollectLabelsFromLSS(lss) ==
    IF lss = <<>> THEN {}
    ELSE {lss[1].label} \cup CollectLabelsFromLSS(Tail(lss))

RECURSIVE CollectLabelsFromProc(_)
CollectLabelsFromProc(p) == CollectLabelsFromLSS(p.body)

RECURSIVE CollectLabelsFromProcSeq(_)
CollectLabelsFromProcSeq(ps) ==
    IF ps = <<>> THEN {}
    ELSE CollectLabelsFromProc(ps[1]) \cup CollectLabelsFromProcSeq(Tail(ps))

RECURSIVE CollectLabelsFromProcess(_)
CollectLabelsFromProcess(pr) == CollectLabelsFromLSS(pr.body)

RECURSIVE CollectLabelsFromProcessSeq(_)
CollectLabelsFromProcessSeq(prs) ==
    IF prs = <<>> THEN {}
    ELSE CollectLabelsFromProcess(prs[1]) \cup CollectLabelsFromProcessSeq(Tail(prs))

CollectAllLabels(ast) ==
    LET procLabels == CollectLabelsFromProcSeq(ast.procedures)
    IN IF ast.algType = "uniprocess"
       THEN procLabels \cup CollectLabelsFromLSS(ast.body)
       ELSE procLabels \cup CollectLabelsFromProcessSeq(ast.processes)

\* Generate VARIABLES declaration
TranslateVariablesSection(ast) ==
    LET globalVarNames == CollectVarNames(ast.globalVars)
        hasStack == ast.procedures # <<>>
        hasPc == TRUE
    IN <<MkKeyword("VARIABLES")>> \o
       <<MkIdent("pc")>> \o
       (IF hasStack THEN <<MkPunct(","), MkIdent("stack")>> ELSE <<>>) \o
       (IF globalVarNames # {} 
        THEN <<MkPunct(",")>> \o TranslateVarDeclSeq(ast.globalVars, "none")
        ELSE <<>>) \o
       <<MkNewline>>

\* Generate Init definition
TranslateInit(ast) ==
    LET globalInits == TranslateVarInitSeq(ast.globalVars, "none")
        pcInit == IF ast.algType = "uniprocess"
                  THEN IF ast.body # <<>>
                       THEN <<MkIdent("pc"), MkOp("="), MkLiteral(ast.body[1].label)>>
                       ELSE <<MkIdent("pc"), MkOp("="), MkLiteral("Done")>>
                  ELSE <<MkIdent("pc"), MkOp("="), MkPunct("["),
                         MkIdent("self"), MkOp("\\in"), MkIdent("ProcSet"),
                         MkOp("|->"), MkLiteral("start"), MkPunct("]")>>
        stackInit == IF ast.procedures # <<>>
                     THEN IF ast.algType = "uniprocess"
                          THEN <<MkOp("/\\"), MkIdent("stack"), MkOp("="), MkPunct("<<"), MkPunct(">>")>>
                          ELSE <<MkOp("/\\"), MkIdent("stack"), MkOp("="), 
                                 MkPunct("["), MkIdent("self"), MkOp("\\in"), MkIdent("ProcSet"),
                                 MkOp("|->"), MkPunct("<<"), MkPunct(">>"), MkPunct("]")>>
                     ELSE <<>>
    IN <<MkIdent("Init"), MkOp("=="), MkNewline, MkIndent(2)>> \o
       pcInit \o <<MkNewline>> \o
       stackInit \o
       (IF globalInits # <<>> THEN <<MkOp("/\\"), MkNewline>> \o globalInits ELSE <<>>) \o
       <<MkNewline>>

\* Generate action for each labeled statement
RECURSIVE TranslateLabeledStmtSeqActions(_, _, _, _)
TranslateLabeledStmtSeqActions(lss, self, procName, allVars) ==
    IF lss = <<>> THEN <<>>
    ELSE LET nextLbl == IF Len(lss) > 1 THEN lss[2].label ELSE "Done"
         IN TranslateLabeledStmt(lss[1], self, nextLbl, procName, allVars) \o
            <<MkNewline, MkNewline>> \o
            TranslateLabeledStmtSeqActions(Tail(lss), self, procName, allVars)

\* Generate Next action
TranslateNext(ast, allLabels) ==
    LET labelDisjuncts == 
        IF ast.algType = "uniprocess"
        THEN <<MkOp("\\/"), MkIdent(CHOOSE l \in allLabels: TRUE)>>
        ELSE <<MkOp("\\/"), MkOp("\\E"), MkIdent("self"), MkOp("\\in"), 
               MkIdent("ProcSet"), MkPunct(":"),
               MkIdent("Action"), MkPunct("("), MkIdent("self"), MkPunct(")")>>
    IN <<MkIdent("Next"), MkOp("=="), MkNewline, MkIndent(2)>> \o
       labelDisjuncts \o
       <<MkNewline, MkOp("\\/"), MkPunct("(")>> \o
       <<MkOp("\\A"), MkIdent("self"), MkOp("\\in"), MkIdent("ProcSet"), 
         MkPunct(":"), MkIdent("pc")>> \o
       (IF ast.algType = "uniprocess" THEN <<>> 
        ELSE <<MkPunct("["), MkIdent("self"), MkPunct("]")>>) \o
       <<MkOp("="), MkLiteral("Done"), MkPunct(")")>> \o
       <<MkOp("/\\"), MkKeyword("UNCHANGED"), MkIdent("vars")>> \o
       <<MkNewline>>

\* Generate Spec formula with fairness
TranslateSpec(ast, fairness) ==
    LET baseSpec == <<MkIdent("Spec"), MkOp("=="), MkIdent("Init"), 
                      MkOp("/\\"), MkPunct("[]"), MkPunct("["), 
                      MkIdent("Next"), MkPunct("]"), MkOp("_"), MkIdent("vars")>>
        fairnessClause ==
            CASE fairness = NoFairness -> <<>>
            [] fairness = WeakFairnessWhole ->
               <<MkOp("/\\"), MkIdent("WF_"), MkIdent("vars"), 
                 MkPunct("("), MkIdent("Next"), MkPunct(")")>>
            [] fairness = WeakFairnessPerAction ->
               <<MkOp("/\\"), MkOp("\\A"), MkIdent("self"), MkOp("\\in"), MkIdent("ProcSet"),
                 MkPunct(":"), MkIdent("WF_"), MkIdent("vars"), 
                 MkPunct("("), MkIdent("Action"), MkPunct("("), MkIdent("self"), MkPunct(")"), MkPunct(")")>>
            [] fairness = StrongFairnessPerAction ->
               <<MkOp("/\\"), MkOp("\\A"), MkIdent("self"), MkOp("\\in"), MkIdent("ProcSet"),
                 MkPunct(":"), MkIdent("SF_"), MkIdent("vars"),
                 MkPunct("("), MkIdent("Action"), MkPunct("("), MkIdent("self"), MkPunct(")"), MkPunct(")")>>
            [] OTHER -> <<>>
    IN baseSpec \o fairnessClause \o <<MkNewline>>

\* Generate Termination property
TranslateTermination(ast) ==
    IF ast.algType = "uniprocess"
    THEN <<MkIdent("Termination"), MkOp("=="), MkPunct("<>"), MkPunct("("),
           MkIdent("pc"), MkOp("="), MkLiteral("Done"), MkPunct(")")>>
    ELSE <<MkIdent("Termination"), MkOp("=="), MkPunct("<>"), MkPunct("("),
           MkOp("\\A"), MkIdent("self"), MkOp("\\in"), MkIdent("ProcSet"),
           MkPunct(":"), MkIdent("pc"), MkPunct("["), MkIdent("self"), MkPunct("]"),
           MkOp("="), MkLiteral("Done"), MkPunct(")")>>

\* Main Translation operator
Translation(ast, fairness) ==
    LET allLabels == CollectAllLabels(ast)
        allVarNames == CollectVarNames(ast.globalVars)
        moduleHeader == <<MkPunct("----"), MkKeyword("MODULE"), MkIdent(ast.name), 
                          MkPunct("----"), MkNewline>>
        extendsClause == <<MkKeyword("EXTENDS"), MkIdent("Naturals"), MkPunct(","),
                          MkIdent("Sequences"), MkNewline, MkNewline>>
        variablesSection == TranslateVariablesSection(ast)
        varsDefn == <<MkIdent("vars"), MkOp("=="), MkPunct("<<"), MkIdent("pc")>> \o
                    (IF ast.procedures # <<>> THEN <<MkPunct(","), MkIdent("stack")>> ELSE <<>>) \o
                    <<MkPunct(">>"), MkNewline, MkNewline>>
        initDefn == TranslateInit(ast)
        nextDefn == TranslateNext(ast, allLabels)
        specDefn == TranslateSpec(ast, fairness)
        termDefn == TranslateTermination(ast)
        moduleFooter == <<MkPunct("====