---------------------------- MODULE Translator ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Object, Any

(***************************************************************************)
(* Helper operators for sequence manipulation                               *)
(***************************************************************************)

Concat(seqs) == 
    IF seqs = <<>> THEN <<>>
    ELSE LET RECURSIVE ConcatRec(_)
             ConcatRec(s) == IF s = <<>> THEN <<>> 
                            ELSE Head(s) \o ConcatRec(Tail(s))
         IN ConcatRec(seqs)

Flatten(seq) == Concat(seq)

SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

SetToSeq(S) == 
    IF S = {} THEN <<>>
    ELSE LET pick == CHOOSE x \in S : TRUE
         IN <<pick>> \o SetToSeq(S \ {pick})

(***************************************************************************)
(* Lexeme constructors                                                      *)
(***************************************************************************)

Lex(s) == <<"LEX", s>>
Ident(s) == <<"IDENT", s>>
Number(n) == <<"NUMBER", n>>
Keyword(s) == <<"KEYWORD", s>>
Newline == <<"NEWLINE">>
Indent == <<"INDENT">>
Dedent == <<"DEDENT">>

(***************************************************************************)
(* Grammar definitions for +CAL AST                                        *)
(***************************************************************************)

(* Variable declaration *)
IsVarDecl(v) ==
    /\ v.type = "VarDecl"
    /\ v.name \in Any
    /\ v.init \in Any

(* Simple statements *)
IsAssignment(s) ==
    /\ s.type = "Assignment"
    /\ s.lhs \in Any
    /\ s.rhs \in Any

IsWhen(s) ==
    /\ s.type = "When"
    /\ s.cond \in Any

IsPrint(s) ==
    /\ s.type = "Print"
    /\ s.expr \in Any

IsAssert(s) ==
    /\ s.type = "Assert"
    /\ s.expr \in Any

IsSkip(s) ==
    s.type = "Skip"

IsSimpleStmt(s) ==
    \/ IsAssignment(s)
    \/ IsWhen(s)
    \/ IsPrint(s)
    \/ IsAssert(s)
    \/ IsSkip(s)

(* Control flow statements *)
IsGoto(s) ==
    /\ s.type = "Goto"
    /\ s.label \in Any

IsReturn(s) ==
    s.type = "Return"

IsCall(s) ==
    /\ s.type = "Call"
    /\ s.proc \in Any
    /\ s.args \in Any

IsCallReturn(s) ==
    /\ s.type = "CallReturn"
    /\ s.proc \in Any
    /\ s.args \in Any

IsIf(s) ==
    /\ s.type = "If"
    /\ s.cond \in Any
    /\ s.then \in Any
    /\ s.else \in Any

IsEither(s) ==
    /\ s.type = "Either"
    /\ s.branches \in Any

IsWith(s) ==
    /\ s.type = "With"
    /\ s.var \in Any
    /\ s.set \in Any
    /\ s.body \in Any

IsWhile(s) ==
    /\ s.type = "While"
    /\ s.cond \in Any
    /\ s.body \in Any

(* Labeled statement *)
IsLabeledStmt(ls) ==
    /\ ls.type = "LabeledStmt"
    /\ ls.label \in Any
    /\ ls.stmts \in Any

(* Procedure definition *)
IsProcedure(p) ==
    /\ p.type = "Procedure"
    /\ p.name \in Any
    /\ p.params \in Any
    /\ p.locals \in Any
    /\ p.body \in Any

(* Process definition *)
IsProcess(p) ==
    /\ p.type = "Process"
    /\ p.name \in Any
    /\ p.id \in Any
    /\ p.idSet \in Any
    /\ p.locals \in Any
    /\ p.body \in Any

(* Algorithm types *)
IsUniprocessAlg(a) ==
    /\ a.type = "UniprocessAlgorithm"
    /\ a.name \in Any
    /\ a.globals \in Any
    /\ a.procedures \in Any
    /\ a.body \in Any

IsMultiprocessAlg(a) ==
    /\ a.type = "MultiprocessAlgorithm"
    /\ a.name \in Any
    /\ a.globals \in Any
    /\ a.procedures \in Any
    /\ a.processes \in Any

IsAlgorithm(a) ==
    \/ IsUniprocessAlg(a)
    \/ IsMultiprocessAlg(a)

(* Fairness options *)
FairnessNone == "none"
FairnessWFActions == "wf_actions"
FairnessWFNext == "wf_next"
FairnessSFActions == "sf_actions"

IsFairnessOption(f) ==
    f \in {FairnessNone, FairnessWFActions, FairnessWFNext, FairnessSFActions}

(***************************************************************************)
(* Helper operators for translation                                        *)
(***************************************************************************)

(* Get all labels from a sequence of labeled statements *)
RECURSIVE GetLabels(_)
GetLabels(stmts) ==
    IF stmts = <<>> THEN {}
    ELSE LET s == Head(stmts)
         IN IF s.type = "LabeledStmt" 
            THEN {s.label} \union GetLabels(Tail(stmts))
            ELSE GetLabels(Tail(stmts))

(* Get all variable names from declarations *)
RECURSIVE GetVarNames(_)
GetVarNames(decls) ==
    IF decls = <<>> THEN {}
    ELSE {Head(decls).name} \union GetVarNames(Tail(decls))

(* Check if algorithm is multiprocess *)
IsMultiprocess(alg) == alg.type = "MultiprocessAlgorithm"

(* Get all process names and IDs *)
RECURSIVE GetProcessInfo(_)
GetProcessInfo(procs) ==
    IF procs = <<>> THEN {}
    ELSE LET p == Head(procs)
         IN {[name |-> p.name, id |-> p.id, idSet |-> p.idSet]} 
            \union GetProcessInfo(Tail(procs))

(***************************************************************************)
(* Expression translation                                                   *)
(***************************************************************************)

RECURSIVE TranslateExpr(_, _)
TranslateExpr(expr, ctx) ==
    CASE expr.type = "Var" -> <<Ident(expr.name)>>
      [] expr.type = "Num" -> <<Number(expr.value)>>
      [] expr.type = "Bool" -> <<Lex(IF expr.value THEN "TRUE" ELSE "FALSE")>>
      [] expr.type = "String" -> <<Lex("\""), Lex(expr.value), Lex("\"")>>
      [] expr.type = "BinOp" -> 
            TranslateExpr(expr.left, ctx) \o <<Lex(" "), Lex(expr.op), Lex(" ")>> 
            \o TranslateExpr(expr.right, ctx)
      [] expr.type = "UnOp" -> 
            <<Lex(expr.op)>> \o TranslateExpr(expr.arg, ctx)
      [] expr.type = "FnApp" ->
            <<Ident(expr.fn), Lex("[")>> \o TranslateExpr(expr.arg, ctx) \o <<Lex("]")>>
      [] expr.type = "Set" ->
            <<Lex("{")>> \o TranslateExpr(expr.elements, ctx) \o <<Lex("}")>>
      [] expr.type = "Record" ->
            <<Lex("[")>> \o TranslateExpr(expr.fields, ctx) \o <<Lex("]")>>
      [] OTHER -> <<Lex(ToString(expr))>>

(* Translate primed variable *)
TranslatePrimedVar(name, ctx) ==
    IF ctx.multiprocess 
    THEN <<Ident(name), Lex("'"), Lex("["), Ident("self"), Lex("]")>>
    ELSE <<Ident(name), Lex("'")>>

(* Translate unprimed variable *)
TranslateUnprimedVar(name, ctx) ==
    IF ctx.multiprocess /\ name \in ctx.localVars
    THEN <<Ident(name), Lex("["), Ident("self"), Lex("]")>>
    ELSE <<Ident(name)>>

(***************************************************************************)
(* Statement translation                                                    *)
(***************************************************************************)

RECURSIVE TranslateStmt(_, _, _)
RECURSIVE TranslateStmts(_, _, _)

TranslateStmt(stmt, ctx, nextLabel) ==
    CASE stmt.type = "Assignment" ->
            TranslatePrimedVar(stmt.lhs, ctx) \o <<Lex(" = ")>> 
            \o TranslateExpr(stmt.rhs, ctx)
      [] stmt.type = "Skip" ->
            <<Lex("TRUE")>>
      [] stmt.type = "When" ->
            TranslateExpr(stmt.cond, ctx)
      [] stmt.type = "Print" ->
            <<Lex("PrintT(")>> \o TranslateExpr(stmt.expr, ctx) \o <<Lex(")")>>
      [] stmt.type = "Assert" ->
            <<Lex("Assert(")>> \o TranslateExpr(stmt.expr, ctx) \o <<Lex(")")>>
      [] stmt.type = "Goto" ->
            <<Ident("pc"), Lex("'")>> \o 
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(" = "), Lex("\""), Lex(stmt.label), Lex("\"")>>
      [] stmt.type = "Return" ->
            <<Ident("pc"), Lex("'")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(" = "), Ident("Head"), Lex("("), Ident("stack")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(").pc"), Newline>> \o
            <<Lex("/\\ "), Ident("stack"), Lex("'")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(" = "), Ident("Tail"), Lex("("), Ident("stack")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(")")>>
      [] stmt.type = "Call" ->
            <<Ident("stack"), Lex("'")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(" = "), Lex("<<"), Lex("[pc |-> \""), Lex(nextLabel), Lex("\"]"), 
              Lex(">> \\o "), Ident("stack")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Newline>> \o
            <<Lex("/\\ "), Ident("pc"), Lex("'")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(" = \""), Lex(stmt.proc), Lex("\"")>>
      [] stmt.type = "CallReturn" ->
            <<Ident("stack"), Lex("'")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(" = "), Lex("<<"), Lex("[pc |-> "), Ident("Head"), Lex("("), 
              Ident("stack")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(").pc]"), Lex(">> \\o "), Ident("Tail"), Lex("("), Ident("stack")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(")"), Newline>> \o
            <<Lex("/\\ "), Ident("pc"), Lex("'")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(" = \""), Lex(stmt.proc), Lex("\"")>>
      [] stmt.type = "If" ->
            <<Lex("IF ")>> \o TranslateExpr(stmt.cond, ctx) \o <<Newline>> \o
            <<Lex("THEN ")>> \o TranslateStmts(stmt.then, ctx, nextLabel) \o <<Newline>> \o
            <<Lex("ELSE ")>> \o TranslateStmts(stmt.else, ctx, nextLabel)
      [] stmt.type = "Either" ->
            LET branches == stmt.branches
                RECURSIVE TranslateBranches(_)
                TranslateBranches(bs) ==
                    IF bs = <<>> THEN <<>>
                    ELSE IF Len(bs) = 1 
                         THEN TranslateStmts(Head(bs), ctx, nextLabel)
                         ELSE TranslateStmts(Head(bs), ctx, nextLabel) \o 
                              <<Newline, Lex("\\/ ")>> \o TranslateBranches(Tail(bs))
            IN <<Lex("\\/ ")>> \o TranslateBranches(branches)
      [] stmt.type = "With" ->
            <<Lex("\\E "), Ident(stmt.var), Lex(" \\in ")>> \o 
            TranslateExpr(stmt.set, ctx) \o <<Lex(":"), Newline>> \o
            TranslateStmts(stmt.body, ctx, nextLabel)
      [] stmt.type = "While" ->
            <<Lex("IF ")>> \o TranslateExpr(stmt.cond, ctx) \o <<Newline>> \o
            <<Lex("THEN ")>> \o TranslateStmts(stmt.body, ctx, nextLabel) \o
            <<Lex(" /\\ "), Ident("pc"), Lex("'")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(" = \""), Lex(ctx.currentLabel), Lex("\""), Newline>> \o
            <<Lex("ELSE "), Ident("pc"), Lex("'")>> \o
            (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
            <<Lex(" = \""), Lex(nextLabel), Lex("\"")>>
      [] OTHER -> <<Lex("TRUE")>>

TranslateStmts(stmts, ctx, nextLabel) ==
    IF stmts = <<>> THEN <<Lex("TRUE")>>
    ELSE IF Len(stmts) = 1 
         THEN TranslateStmt(Head(stmts), ctx, nextLabel)
         ELSE TranslateStmt(Head(stmts), ctx, nextLabel) \o 
              <<Newline, Lex("/\\ ")>> \o TranslateStmts(Tail(stmts), ctx, nextLabel)

(***************************************************************************)
(* UNCHANGED clause generation                                              *)
(***************************************************************************)

GenerateUnchanged(changedVars, allVars) ==
    LET unchanged == allVars \ changedVars
    IN IF unchanged = {} THEN <<>>
       ELSE <<Newline, Lex("/\\ UNCHANGED <<")>> \o
            LET varSeq == SetToSeq(unchanged)
                RECURSIVE VarList(_)
                VarList(vs) ==
                    IF vs = <<>> THEN <<>>
                    ELSE IF Len(vs) = 1 THEN <<Ident(Head(vs))>>
                         ELSE <<Ident(Head(vs)), Lex(", ")>> \o VarList(Tail(vs))
            IN VarList(varSeq) \o <<Lex(">>")>>

(***************************************************************************)
(* Action translation for labeled statements                                *)
(***************************************************************************)

TranslateLabeledAction(ls, ctx, nextLabel) ==
    LET label == ls.label
        stmts == ls.stmts
        actionCtx == [ctx EXCEPT !.currentLabel = label]
    IN <<Ident(label)>> \o 
       (IF ctx.multiprocess THEN <<Lex("("), Ident("self"), Lex(")")>> ELSE <<>>) \o
       <<Lex(" == "), Newline>> \o
       <<Lex("/\\ "), Ident("pc")>> \o
       (IF ctx.multiprocess THEN <<Lex("["), Ident("self"), Lex("]")>> ELSE <<>>) \o
       <<Lex(" = \""), Lex(label), Lex("\""), Newline>> \o
       <<Lex("/\\ ")>> \o TranslateStmts(stmts, actionCtx, nextLabel)

(***************************************************************************)
(* Variable declarations translation                                        *)
(***************************************************************************)

RECURSIVE TranslateVarDecls(_)
TranslateVarDecls(decls) ==
    IF decls = <<>> THEN <<>>
    ELSE LET d == Head(decls)
         IN <<Ident(d.name), Lex(" = ")>> \o TranslateExpr(d.init, [multiprocess |-> FALSE, localVars |-> {}]) \o
            (IF Len(decls) > 1 THEN <<Lex(","), Newline>> ELSE <<>>) \o
            TranslateVarDecls(Tail(decls))

(***************************************************************************)
(* Init predicate translation                                               *)
(***************************************************************************)

TranslateInit(alg) ==
    LET globals == alg.globals
        isMulti == IsMultiprocess(alg)
    IN <<Ident("Init"), Lex(" == "), Newline>> \o
       (IF globals # <<>> 
        THEN <<Lex("/\\ ")>> \o TranslateVarDecls(globals) \o <<Newline>>
        ELSE <<>>) \o
       <<Lex("/\\ "), Ident("pc"), Lex(" = ")>> \o
       (IF isMulti 
        THEN <<Lex("[self \\in ProcSet |-> CASE ")>> \o
             LET procs == alg.processes
                 RECURSIVE ProcCases(_)
                 ProcCases(ps) ==
                     IF ps = <<>> THEN <<Lex("\"Done\"")>>
                     ELSE LET p == Head(ps)
                          IN <<Lex("self \\in "), Lex(ToString(p.idSet)), 
                               Lex(" -> \""), Lex(Head(p.body).label), Lex("\"")>> \o
                             (IF Len(ps) > 1 THEN <<Newline, Lex("[] ")>> ELSE <<>>) \o
                             ProcCases(Tail(ps))
             IN ProcCases(procs) \o <<Lex("]")>>
        ELSE <<Lex("\""), Lex(Head(alg.body).label), Lex("\"")>>) \o
       <<Newline>> \o
       (IF alg.procedures # <<>> 
        THEN <<Lex("/\\ "), Ident("stack"), Lex(" = ")>> \o
             (IF isMulti THEN <<Lex("[self \\in ProcSet |-> <<>>]")>>
              ELSE <<Lex("<<>>")>>) \o <<Newline>>
        ELSE <<>>)

(***************************************************************************)
(* Next-state action translation                                            *)
(***************************************************************************)

TranslateNext(alg, labels) ==
    LET isMulti == IsMultiprocess(alg)
        labelSeq == SetToSeq(labels)
        RECURSIVE ActionDisjuncts(_)
        ActionDisjuncts(ls) ==
            IF ls = <<>> THEN <<>>
            ELSE <<Lex("\\/ "), Ident(Head(ls))>> \o
                 (IF isMulti THEN <<Lex("(self)")>> ELSE <<>>) \o
                 (IF Len(ls) > 1 THEN <<Newline>> ELSE <<>>) \o
                 ActionDisjuncts(Tail(ls))
    IN <<Ident("Next"), Lex(" == ")>> \o
       (IF isMulti 
        THEN <<Lex("\\E self \\in ProcSet:"), Newline>>
        ELSE <<Newline>>) \o
       ActionDisjuncts(labelSeq) \o
       <<Newline, Lex("\\/ (* Stuttering *)"), Newline>> \o
       <<Lex("/\\ "), Ident("pc")>> \o
       (IF isMulti THEN <<Lex(" = [self \\in ProcSet |-> \"Done\"]")>>
        ELSE <<Lex(" = \"Done\"")>>) \o
       <<Newline, Lex("/\\ UNCHANGED vars")>>

(***************************************************************************)
(* Spec formula translation                                                 *)
(***************************************************************************)

TranslateSpec(alg, fairness, labels) ==
    LET isMulti == IsMultiprocess(alg)
    IN <<Ident("Spec"), Lex(" == "), Ident("Init"), Lex(" /\\ []["), 
        Ident("Next"), Lex("]_vars")>> \o
       CASE fairness = FairnessNone -> <<>>
         [] fairness = FairnessWFNext -> <<Lex(" /\\ WF_vars("), Ident("Next"), Lex(")")>>
         [] fairness = FairnessWFActions ->
              LET labelSeq == SetToSeq(labels)
                  RECURSIVE WFClauses(_)
                  WFClauses(ls) ==
                      IF ls = <<>> THEN <<>>
                      ELSE <<Newline, Lex("/\\ ")>> \o
                           (IF isMulti 
                            THEN <<Lex("\\A self \\in ProcSet: WF_vars("), Ident(Head(ls)), Lex("(self))")>>
                            ELSE <<Lex("WF_vars("), Ident(Head(ls)), Lex(")")>>) \o
                           WFClauses(Tail(ls))
              IN WFClauses(labelSeq)
         [] fairness = FairnessSFActions ->
              LET labelSeq == SetToSeq(labels)
                  RECURSIVE SFClauses(_)
                  SFClauses(ls) ==
                      IF ls = <<>> THEN <<>>
                      ELSE <<Newline, Lex("/\\ ")>> \o
                           (IF isMulti 
                            THEN <<Lex("\\A self \\in ProcSet: SF_vars("), Ident(Head(ls)), Lex("(self))")>>
                            ELSE <<Lex("SF_vars("), Ident(Head(ls)), Lex(")")>>) \o
                           SFClauses(Tail(ls))
              IN SFClauses(labelSeq)
         [] OTHER -> <<>>

(***************************************************************************)
(* Termination property                                                     *)
(***************************************************************************)

TranslateTermination(alg) ==
    LET isMulti == IsMultiprocess(alg)
    IN <<Ident("Termination"), Lex(" == <>"), Lex("(")>> \o
       (IF isMulti 
        THEN <<Lex("\\A self \\in ProcSet: "), Ident("pc"), Lex("[self] = \"Done\"")>>
        ELSE <<Ident("pc"), Lex(" = \"Done\"")>>) \o
       <<Lex(")")>>

(***************************************************************************)
(* Collect all labels from algorithm                                        *)
(***************************************************************************)

RECURSIVE CollectLabelsFromBody(_)
CollectLabelsFromBody(body) ==
    IF body = <<>> THEN {}
    ELSE LET ls == Head(body)
         IN (IF ls.type = "LabeledStmt" THEN {ls.label} ELSE {}) 
            \union CollectLabelsFromBody(Tail(body))

CollectAllLabels(alg) ==
    LET bodyLabels == IF IsMultiprocess(alg) 
                      THEN LET procs == alg.processes
                               RECURSIVE ProcLabels(_)
                               ProcLabels(ps) ==
                                   IF ps = <<>> THEN {}
                                   ELSE CollectLabelsFromBody(Head(ps).body) 
                                        \union ProcLabels(Tail(ps))
                           IN ProcLabels(procs)
                      ELSE CollectLabelsFromBody(alg.body)
        procLabels == LET procs == alg.procedures
                          RECURSIVE GetProcLabels(_)
                          GetProcLabels(ps) ==
                              IF ps = <<>> THEN {}
                              ELSE CollectLabelsFromBody(Head(ps).body) 
                                   \union GetProcLabels(Tail(ps))
                      IN GetProcLabels(procs)
    IN bodyLabels \union procLabels

(***************************************************************************)
(* Main Translation operator                                                *)
(***************************************************************************)

Translation(alg, fairness) ==
    LET labels == CollectAllLabels(alg)
        isMulti == IsMultiprocess(alg)
        
        moduleHeader == <<Lex("---- MODULE "), Ident(alg.name), Lex(" ----"), Newline>>
        
        extendsClause == <<Lex("EXTENDS Naturals, Sequences, TLC"), Newline, Newline>>
        
        varsDecl == <<Lex("VARIABLES "), Ident("pc")>> \o
                    (IF alg.procedures # <<>> THEN <<Lex(", "), Ident("stack")>> ELSE <<>>) \o
                    (IF alg.globals # <<>> 
                     THEN LET RECURSIVE VarNames(_)
                              VarNames(gs) ==
                                  IF gs = <<>> THEN <<>>
                                  ELSE <<Lex(", "), Ident(Head(gs).name)>> \o VarNames(Tail(gs))
                          IN VarNames(alg.globals)
                     ELSE <<>>) \o
                    <<Newline, Newline>>
        
        varsTuple == <<Lex("vars == <<"), Ident("pc")>> \o
                     (IF alg.procedures # <<>> THEN <<Lex(", "), Ident("stack")>> ELSE <<>>) \o
                     (IF alg.globals # <<>> 
                      THEN LET RECURSIVE VarNames2(_)
                               VarNames2(gs) ==
                                   IF gs = <<>> THEN <<>>
                                   ELSE <<Lex(", "), Ident(Head(gs).name)>> \o VarNames2(Tail(gs))
                           IN VarNames2(alg.globals)
                      ELSE <<>>) \o
                     <<Lex(">>"), Newline, Newline>>
        
        procSet == IF isMulti 
                   THEN <<Lex("ProcSet == ")>> \o
                        LET procs == alg.processes
                            RECURSIVE ProcSets(_)
                            ProcSets(ps) ==
                                IF ps = <<>> THEN <<>>
                                ELSE <<Lex(ToString(Head(ps).idSet))>> \o
                                     (IF Len(ps) > 1 THEN <<Lex(" \\union ")>> ELSE <<>>) \o
                                     ProcSets(Tail(ps))
                        IN ProcSets(procs) \o <<Newline, Newline>>
                   ELSE <<>>
        
        initDef == TranslateInit(alg) \o <<Newline, Newline>>
        
        ctx == [multiprocess |-> isMulti, 
                localVars |-> {},
                currentLabel |-> ""]
        
        labelSeq == SetToSeq(labels)
        RECURSIVE ActionDefs(_)
        ActionDefs(ls) ==
            IF ls = <<>> THEN <<>>
            ELSE TranslateLabeledAction([type |-> "LabeledStmt", label |-> Head(ls), stmts |-> <<>>], 
                                        ctx, "Done") \o
                 <<Newline, Newline>> \o ActionDefs(Tail(ls))
        
        actionDefs == ActionDefs(labelSeq)
        
        nextDef == TranslateNext(alg, labels) \o <<Newline, Newline>>
        
        specDef == TranslateSpec(alg, fairness, labels) \o <<Newline, Newline>>
        
        terminationDef == TranslateTermination(alg) \o <<Newline, Newline>>
        
        moduleFooter == <<Lex("====