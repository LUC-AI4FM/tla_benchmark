------------------------------ MODULE OldPlusCal ------------------------------
EXTENDS Sequences

CONSTANTS ast, fairness

(* Grammar definitions *)
AlgAST          == Seq(String)
ProcedureAST    == Seq(String)
ProcessAST      == Seq(String)
VarDeclAST      == Seq(String)
LabelStmtAST    == Seq(String)
WhileLoopAST    == Seq(String)
LabelSeqAST     == Seq(String)
SimpleStmtAST   == Seq(String)
CallReturnAST   == Seq(String)
GotoAST         == Seq(String)
ExprLexemes     == Seq(String)

IsAlgAST(a)          == a \in AlgAST
IsProcedureAST(p)   == p \in ProcedureAST
IsProcessAST(pr)    == pr \in ProcessAST
IsVarDecl(vd)       == vd \in VarDeclAST
IsLabelStmt(ls)     == ls \in LabelStmtAST
IsWhileLoop(wl)     == wl \in WhileLoopAST
IsLabelSeq(lsq)     == lsq \in LabelSeqAST
IsSimpleStmt(ss)    == ss \in SimpleStmtAST
IsCallReturn(cr)    == cr \in CallReturnAST
IsGoto(g)           == g \in GotoAST

(* Exploding labeled statements *)
FullyExplodeSeq(seq) == seq
Explode(stmt)       == stmt

(* Generate components of the TLA+ spec *)
GenerateInit(alg)          == << "INIT" >>
GenerateNext(alg)          == << "NEXT" >>
GenerateSpec(alg)          == << "SPEC" >>
GenerateProcSet(alg)       == << "PROCSET" >>
GenerateVars(alg)          == << "VARS" >>
GenerateTermination(alg)   == << "TERMINATION" >>

(* Fairness lexemes *)
FairnessLex(fairnessOption) ==
  CASE fairnessOption = ""      -> <<>>
       fairnessOption = "wf"    -> << "WF", "Next" >>
       fairnessOption = "wfNext"-> << "WF", "Next" >>
       fairnessOption = "sf"    -> << "SF" >>
       TRUE                     -> <<>>

(* Translate a sequence of statements into TLA+ lexemes *)
TranslateSeq(seq, fairnessOption) ==
  LET
    init     == GenerateInit(seq)
    next     == GenerateNext(seq)
    spec     == GenerateSpec(seq)
    procSet  == GenerateProcSet(seq)
    vars     == GenerateVars(seq)
    term     == GenerateTermination(seq)
    fairLex  == FairnessLex(fairnessOption)
  IN
    init ~ next ~ spec ~ procSet ~ vars ~ term ~ fairLex

(* Main translation operator *)
Translation(alg, fairnessOption) ==
  LET
    exploded   == FullyExplodeSeq(alg)
    translated == TranslateSeq(exploded, fairnessOption)
  IN
    translated

ASSUME
  Translation(ast, fairness) \in Seq(String)

=============================================================================