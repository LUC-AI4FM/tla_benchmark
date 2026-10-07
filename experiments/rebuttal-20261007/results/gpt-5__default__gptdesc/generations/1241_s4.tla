---------------------------- MODULE PlusCalTranslate ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

(*
  This module models a translation from a global-naming PlusCal AST to a TLA+ spec.
  It defines a grammar (via well-formedness predicates) and translation operators
  that emit sequences of lexemes containing Init, Next, Spec, and a Termination
  property. It also models fairness options for the generated spec.
*)

CONSTANTS
  ALGNAME,      \* Set of possible algorithm names (model values or strings)
  VAR,          \* Set of possible variable identifiers
  PROCNAME,     \* Set of possible procedure identifiers
  PROCESSNAME,  \* Set of possible process names
  LABEL,        \* Set of possible statement labels
  EXPR,         \* Set of (opaque) expression nodes
  VALUE         \* Set of values used in RHS etc.

(*
  State variables of the meta-translation system:
    - alg:    an AST record of kind "Alg"
    - out:    the resulting sequence of lexemes (strings or model values) after translation
    - done:   TRUE after translation has completed
    - fairSel: chosen fairness option for the generated spec
    - step:   simple control to drive translation: "Translate" -> "Done"
*)
VARIABLES alg, out, done, fairSel, step

FairnessOpts == {"None", "WF_Procs", "WF_Next", "SF_Procs"}

(***************************************************************************)
(*                        Grammar and Well-Formedness                      *)
(***************************************************************************)

IsSeq(s) == \E n \in Nat: DOMAIN s = 1..n

RECURSIVE WFStmt(_), WFStmtSeq(_)

WFStmtSeq(ss) ==
  IsSeq(ss)
  /\ \A i \in DOMAIN ss : WFStmt(ss[i])

WFGuard(g) ==
  /\ g \in [cond: EXPR, body: Seq({})]  \* type shape
  /\ WFStmtSeq(g.body)

WFAssign(s) ==
  /\ DOMAIN s = {"kind", "lhs", "rhs"}
  /\ s.kind = "Assign"
  /\ s.lhs \in VAR
  /\ s.rhs \in EXPR

WFIf(s) ==
  /\ DOMAIN s = {"kind", "guards", "other"}
  /\ s.kind = "If"
  /\ IsSeq(s.guards)
  /\ \A i \in DOMAIN s.guards : WFGuard(s.guards[i])
  /\ WFStmtSeq(s.other)

WFWhile(s) ==
  /\ DOMAIN s = {"kind", "cond", "body"}
  /\ s.kind = "While"
  /\ s.cond \in EXPR
  /\ WFStmtSeq(s.body)

WFGoto(s) ==
  /\ DOMAIN s = {"kind", "label"}
  /\ s.kind = "Goto"
  /\ s.label \in LABEL

WFLabel(s) ==
  /\ DOMAIN s = {"kind", "name", "body"}
  /\ s.kind = "Label"
  /\ s.name \in LABEL
  /\ WFStmtSeq(s.body)

WFCall(s) ==
  /\ DOMAIN s = {"kind", "proc", "args"}
  /\ s.kind = "Call"
  /\ s.proc \in PROCNAME
  /\ IsSeq(s.args)
  /\ \A i \in DOMAIN s.args : s.args[i] \in EXPR

WFWith(s) ==
  /\ DOMAIN s = {"kind", "var", "domain", "body"}
  /\ s.kind = "With"
  /\ s.var \in VAR
  /\ s.domain \in EXPR
  /\ WFStmtSeq(s.body)

WFSkip(s) ==
  /\ DOMAIN s = {"kind"}
  /\ s.kind = "Skip"

WFReturn(s) ==
  /\ DOMAIN s = {"kind"}
  /\ s.kind = "Return"

WFEither(s) ==
  /\ DOMAIN s = {"kind", "branches"}
  /\ s.kind = "Either"
  /\ IsSeq(s.branches)
  /\ \A i \in DOMAIN s.branches : WFStmtSeq(s.branches[i])

WFAwait(s) ==
  /\ DOMAIN s = {"kind", "cond"}
  /\ s.kind = "Await"
  /\ s.cond \in EXPR

WFStmt(s) ==
  WFAssign(s) \/
  WFIf(s)     \/
  WFWhile(s)  \/
  WFGoto(s)   \/
  WFLabel(s)  \/
  WFCall(s)   \/
  WFWith(s)   \/
  WFSkip(s)   \/
  WFReturn(s) \/
  WFEither(s) \/
  WFAwait(s)

WFProc(p) ==
  /\ DOMAIN p = {"kind", "name", "params", "locals", "body"}
  /\ p.kind = "Proc"
  /\ p.name \in PROCNAME
  /\ IsSeq(p.params) /\ \A i \in DOMAIN p.params : p.params[i] \in VAR
  /\ IsSeq(p.locals) /\ \A i \in DOMAIN p.locals : p.locals[i] \in VAR
  /\ WFStmtSeq(p.body)

WFProcess(pr) ==
  /\ DOMAIN pr = {"kind", "name", "locals", "body"}
  /\ pr.kind = "Process"
  /\ pr.name \in PROCESSNAME
  /\ IsSeq(pr.locals) /\ \A i \in DOMAIN pr.locals : pr.locals[i] \in VAR
  /\ WFStmtSeq(pr.body)

SeqToSet(s) == { s[i] : i \in DOMAIN s }
Distinct(s) == IsSeq(s) /\ Cardinality(SeqToSet(s)) = Len(s)

NamesOfProcs(ps) == { ps[i].name : i \in DOMAIN ps }
NamesOfProcsDistinct(ps) == IsSeq(ps) /\ Distinct([i \in DOMAIN ps |-> ps[i].name])

NamesOfProcesses(ps) == { ps[i].name : i \in DOMAIN ps }
NamesOfProcessesDistinct(ps) == IsSeq(ps) /\ Distinct([i \in DOMAIN ps |-> ps[i].name])

WFAlg(a) ==
  /\ DOMAIN a = {"kind", "name", "vars", "procs", "processes", "fairness"}
  /\ a.kind = "Alg"
  /\ a.name \in ALGNAME
  /\ a.fairness \in FairnessOpts
  /\ IsSeq(a.vars) /\ \A i \in DOMAIN a.vars : a.vars[i] \in VAR /\ Distinct(a.vars)
  /\ IsSeq(a.procs) /\ \A i \in DOMAIN a.procs : WFProc(a.procs[i]) /\ NamesOfProcsDistinct(a.procs)
  /\ IsSeq(a.processes) /\ \A i \in DOMAIN a.processes : WFProcess(a.processes[i]) /\ NamesOfProcessesDistinct(a.processes)

(***************************************************************************)
(*                          Translation to Lexemes                         *)
(***************************************************************************)

RECURSIVE TLStmt(_), TLStmtSeq(_)

(*
  Join a sequence with commas: e.g., <<a,b,c>> -> <<a, ",", b, ",", c>>
*)
RECURSIVE JoinCommaSeq(_)
JoinCommaSeq(s) ==
  IF s = << >> THEN << >>
  ELSE IF Len(s) = 1 THEN << s[1] >>
  ELSE << s[1], "," >> \o JoinCommaSeq(SubSeq(s, 2, Len(s)))

(*
  Statement translation: produces a sequence of lexemes (strings/model values).
  This is schematic; EXPR and VAR are already lexemes by assumption.
*)
TLStmt(s) ==
  IF s.kind = "Assign" THEN << s.lhs, "=", s.rhs, ";" >>
  ELSE IF s.kind = "If" THEN
    (*
      "IF cond1 THEN ... ELSIF cond2 THEN ... ELSE ... END IF;"
      We emit a schematic lexeme sequence.
    *)
    LET G ==
          [i \in DOMAIN s.guards |-> 
            << "IF", s.guards[i].cond, "THEN" >> \o TLStmtSeq(s.guards[i].body) ]
        IN
      (*
        Concatenate guarded branches, inserting "ELSIF" between subsequent ones.
      *)
      LET ConcatGuards(i) ==
            IF i = Len(s.guards) THEN G[i]
            ELSE G[i] \o << "ELSIF" >> \o ConcatGuards(i+1)
      IN (IF Len(s.guards) = 0
          THEN << "IF", "TRUE", "THEN" >> \o TLStmtSeq(<< >>)
          ELSE ConcatGuards(1))
         \o (IF s.other = << >> THEN << "END", "IF", ";" >> ELSE << "ELSE" >> \o TLStmtSeq(s.other) \o << "END", "IF", ";" >>)
  ELSE IF s.kind = "While" THEN
    << "WHILE", s.cond, "DO" >> \o TLStmtSeq(s.body) \o << "END", "WHILE", ";" >>
  ELSE IF s.kind = "Goto" THEN
    << "goto", s.label, ";" >>
  ELSE IF s.kind = "Label" THEN
    << s.name, ":" >> \o TLStmtSeq(s.body)
  ELSE IF s.kind = "Call" THEN
    << s.proc, "(", >> \o JoinCommaSeq(s.args) \o << ")", ";" >>
  ELSE IF s.kind = "With" THEN
    << "with", s.var, "in", s.domain, "do" >> \o TLStmtSeq(s.body) \o << "end", "with", ";" >>
  ELSE IF s.kind = "Skip" THEN
    << "skip", ";" >>
  ELSE IF s.kind = "Return" THEN
    << "return", ";" >>
  ELSE IF s.kind = "Either" THEN
    (*
      either ... or ... end either;
    *)
    LET B == [i \in DOMAIN s.branches |-> TLStmtSeq(s.branches[i])]
        ConcatBranches(i) ==
          IF i = Len(s.branches) THEN << "or" >> \o B[i]
          ELSE << "or" >> \o B[i] \o ConcatBranches(i+1)
    IN << "either" >> \o
       (IF Len(s.branches) = 0 THEN << "skip", ";" >> ELSE B[1] \o (IF Len(s.branches) > 1 THEN ConcatBranches(2) ELSE << >>))
       \o << "end", "either", ";" >>
  ELSE IF s.kind = "Await" THEN
    << "await", s.cond, ";" >>
  ELSE
    << "/*", "UNKNOWN_STMT", "*/" >>

TLStmtSeq(ss) ==
  IF ss = << >> THEN << >>
  ELSE TLStmt(ss[1]) \o TLStmtSeq(SubSeq(ss, 2, Len(ss)))

(*
  Translation of an entire algorithm skeleton:
    MODULE <name> EXTENDS Naturals, Sequences
    VARIABLES ...
    Init == ...
    Next == ...
    Spec == Init /\ [][Next]_vars /\ (fairness clauses)
    Termination == <> Terminated
*)
TLHeader(a) ==
  << "MODULE", a.name, "EXTENDS", "Naturals", "Sequences" >>

TLVarDecl(a) ==
  << "VARIABLES" >> \o JoinCommaSeq(a.vars)

TLInit(a) ==
  << "Init", "==", "TRUE" >>

TLNext(a) ==
  << "Next", "==", "TRUE" >>

(*
  Fairness encoding in the generated Spec
*)
TLFairnessLexemes(f) ==
  CASE f = "None"     -> << >>
     [] f = "WF_Next" -> << "/\\", "WF_vars", "(", "Next", ")" >>
     [] f = "WF_Procs"-> << "/\\", "WF_Procs" >>
     [] f = "SF_Procs"-> << "/\\", "SF_Procs" >>
     OTHER            -> << >>

TLSpec(a) ==
  LET base == << "Spec", "==", "Init", "/\\", "[]", "[", "Next", "]", "_", "vars" >>
  IN base \o TLFairnessLexemes(a.fairness)

TLTermination(a) ==
  << "Termination", "==", "<>", "Terminated" >>

(*
  Combine all parts of the generated TLA+ text as lexemes
*)
TLAlg(a) ==
  TLHeader(a)
  \o TLVarDecl(a)
  \o TLInit(a)
  \o TLNext(a)
  \o TLSpec(a)
  \o TLTermination(a)

(***************************************************************************)
(*                       Output Well-Formedness Checks                     *)
(***************************************************************************)

RECURSIVE SubseqAppears(_, _)

SubseqAppears(s, t) ==
  IF t = << >> THEN TRUE
  ELSE IF s = << >> THEN FALSE
  ELSE IF s[1] = t[1] THEN SubseqAppears(SubSeq(s, 2, Len(s)), SubSeq(t, 2, Len(t)))
  ELSE SubseqAppears(SubSeq(s, 2, Len(s)), t)

OccursToken(s, tok) == \E i \in 1..Len(s) : s[i] = tok

NoFairnessTokens(s) ==
  /\ ~OccursToken(s, "WF_vars")
  /\ ~OccursToken(s, "WF_Procs")
  /\ ~OccursToken(s, "SF_Procs")

OutputEncodesCore(out_) ==
  /\ SubseqAppears(out_, << "Init" >>)
  /\ SubseqAppears(out_, << "Next" >>)
  /\ SubseqAppears(out_, << "Spec" >>)
  /\ SubseqAppears(out_, << "Termination" >>)

OutputEncodesFairness(out_, f) ==
  CASE f = "None"     -> NoFairnessTokens(out_)
     [] f = "WF_Next" -> SubseqAppears(out_, << "WF_vars", "(", "Next", ")" >>)
     [] f = "WF_Procs"-> OccursToken(out_, "WF_Procs")
     [] f = "SF_Procs"-> OccursToken(out_, "SF_Procs")
     OTHER            -> FALSE

OutputEncodes(out_, f) ==
  OutputEncodesCore(out_) /\ OutputEncodesFairness(out_, f)

(***************************************************************************)
(*                          System Init/Next/Spec                          *)
(***************************************************************************)

vars == << alg, out, done, fairSel, step >>

Init ==
  /\ done = FALSE
  /\ out = << >>
  /\ step = "Translate"
  /\ fairSel \in FairnessOpts
  /\ WFAlg(alg)
  /\ alg.fairness = fairSel

DoTranslate ==
  /\ step = "Translate"
  /\ ~done
  /\ out' = TLAlg(alg)
  /\ done' = TRUE
  /\ step' = "Done"
  /\ UNCHANGED << alg, fairSel >>

Stutter ==
  /\ step = "Done"
  /\ UNCHANGED vars

Next == DoTranslate \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(DoTranslate)

(***************************************************************************)
(*                      Safety Invariants and Liveness                     *)
(***************************************************************************)

InvWFAlg == WFAlg(alg)

InvOutputWellFormed == done => OutputEncodes(out, fairSel)

InvStepDoneAgreement == (step = "Done") <=> done

Termination == <> done

=============================================================================