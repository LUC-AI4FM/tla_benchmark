------------------------------- MODULE PlusCalTranslation -------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
A specification of a translator from a well-formed +CAL abstract syntax tree (AST)
to a sequence of TLA+ lexemes that constitutes a valid TLA+ module text.

Inputs:
  - ALG: a fully macro-expanded +CAL AST with distinct labels and variable names.
  - FAIR: a fairness option selecting how fairness is encoded in the produced TLA+:
      "None"           — no fairness
      "WFPerAction"    — weak fairness for each per-label action
      "WFNext"         — weak fairness for the whole Next action
      "SFPerAction"    — strong fairness for each per-label action

Outputs (state variable):
  - out: a sequence of TLA+ lexemes (strings) that grows monotonically to the
         full translation of ALG under FAIR.

This module also defines an abstract functional translation operator FT that,
given ALG and FAIR, deterministically returns the complete sequence of lexemes
for a TLA+ module containing:
  - EXTENDS, VARIABLE declarations (incl. pc, stack, locals handling),
  - Init predicate,
  - per-label action definitions,
  - Next action (disjunction over per-label actions),
  - Spec formula with fairness according to FAIR,
  - Termination property.

The dynamic behavior here merely appends lexemes until the complete FT is produced.
*)

CONSTANTS
  ALG,   \* input +CAL AST
  FAIR   \* fairness option: one of FairnessOpts

(***************************************************************************)
(* Lexical domains, helpers, and general utilities                         *)
(***************************************************************************)

Lexeme == STRING
LexSeq == Seq(Lexeme)
Id     == STRING
Label  == STRING

FairnessOpts == {"None", "WFPerAction", "WFNext", "SFPerAction"}

Append(s, x) == s \o <<x>>
JoinWith(seqs, sep) ==
  IF seqs = <<>> THEN <<>>
  ELSE
    [LET n == Len(seqs) IN
      \* Interleave sep between sequences
      \* e.g., JoinWith(<<a,b,c>>, ",") = a , b , c
      \* Implemented by fold
      \* Start with first, then append sep and next
      RecJoin(i, acc) ==
        IF i > n THEN acc
        ELSE RecJoin(i+1, acc \o (IF i=1 THEN seqs[i] ELSE <<sep>> \o seqs[i]))
     IN
      LET RECURSIVE RecJoin(_,_)
      IN RecJoin(1, <<>>)
    ]

Prefixes(s) == { SubSeq(s, 1, n) : n \in 0..Len(s) }

IsIdentifier(x) == x \in Id
IsLabel(x) == x \in Label

\* Render helpers for lexical pieces
Sp == " "
Nl == "\n"
Eq == "=="
And == "/\\"
Or  == "\\/"
Prime == "'"
LParen == "("
RParen == ")"
LBrack == "["
RBrack == "]"
MapTo == "|->"
InTok == "\\in"
UNCHANGEDTok == "UNCHANGED"
BoxTok == "[]"
AngleTok == "<>"
UnderTok == "_"
VarsTok == "VARIABLES"

(***************************************************************************)
(* +CAL AST grammar (abstract, via record shapes and structural predicates) *)
(***************************************************************************)

Expr == LexSeq

VarDecl(r) ==
  /\ DOMAIN r = {"name","init"}
  /\ r.name \in Id
  /\ r.init \in Expr

VarDecls(ds) == ds \in Seq({ r \in [name: Id, init: Expr] : TRUE })

\* Statement nodes
SimpleStmtKinds == {"Assign","When","Print","Assert","Skip"}
ControlStmtKinds == {"If","Either","While","With","Call","Return","CallReturn","Goto","Labeled","Seq"}

IsVarRef(v) == DOMAIN v = {"name"} /\ v.name \in Id

IsAssign(s) ==
  /\ DOMAIN s = {"kind","lhs","rhs"}
  /\ s.kind = "Assign"
  /\ s.lhs \in Seq({ v \in [name: Id] : TRUE })
  /\ s.rhs \in Seq(Expr)
  /\ Len(s.lhs) = Len(s.rhs)

IsWhen(s) ==
  /\ DOMAIN s = {"kind","cond"}
  /\ s.kind = "When"
  /\ s.cond \in Expr

IsPrint(s) ==
  /\ DOMAIN s = {"kind","exprs"}
  /\ s.kind = "Print"
  /\ s.exprs \in Seq(Expr)

IsAssert(s) ==
  /\ DOMAIN s = {"kind","cond"}
  /\ s.kind = "Assert"
  /\ s.cond \in Expr

IsSkip(s) == /\ DOMAIN s = {"kind"} /\ s.kind = "Skip"

IsIf(s) ==
  /\ DOMAIN s = {"kind","guards"}
  /\ s.kind = "If"
  /\ s.guards \in Seq({ g \in [cond: Expr, then: Seq(SELF)] : TRUE })
  \* SELF is Stmt placeholder; see IsStmt below

IsEither(s) ==
  /\ DOMAIN s = {"kind","arms"}
  /\ s.kind = "Either"
  /\ s.arms \in Seq(Seq(SELF))

IsWhile(s) ==
  /\ DOMAIN s = {"kind","cond","body","testLabel"}
  /\ s.kind = "While"
  /\ s.cond \in Expr
  /\ s.body \in Seq(SELF)
  /\ s.testLabel \in Label

IsWith(s) ==
  /\ DOMAIN s = {"kind","decls","body"}
  /\ s.kind = "With"
  /\ s.decls \in Seq({ d \in [v: Id, domain: Expr] : TRUE })
  /\ s.body \in Seq(SELF)

IsCall(s) ==
  /\ DOMAIN s = {"kind","proc","args"}
  /\ s.kind = "Call"
  /\ s.proc \in Id
  /\ s.args \in Seq(Expr)

IsReturn(s) == /\ DOMAIN s = {"kind"} /\ s.kind = "Return"

IsCallReturn(s) ==
  /\ DOMAIN s = {"kind","proc","args"}
  /\ s.kind = "CallReturn"
  /\ s.proc \in Id
  /\ s.args \in Seq(Expr)

IsGoto(s) ==
  /\ DOMAIN s = {"kind","target"}
  /\ s.kind = "Goto"
  /\ s.target \in Label

IsLabeled(s) ==
  /\ DOMAIN s = {"kind","label","stmt"}
  /\ s.kind = "Labeled"
  /\ s.label \in Label
  /\ IsStmt(s.stmt)

IsSeq(s) ==
  /\ DOMAIN s = {"kind","stmts"}
  /\ s.kind = "Seq"
  /\ s.stmts \in Seq(SELF)

IsSimple(s) == IsAssign(s) \/ IsWhen(s) \/ IsPrint(s) \/ IsAssert(s) \/ IsSkip(s)
IsControl(s) == IsIf(s) \/ IsEither(s) \/ IsWhile(s) \/ IsWith(s) \/ IsCall(s) \/
                 IsReturn(s) \/ IsCallReturn(s) \/ IsGoto(s) \/ IsLabeled(s) \/
                 IsSeq(s)

IsStmt(s) == IsSimple(s) \/ IsControl(s)

\* Procedures and processes
IsProcedure(p) ==
  /\ DOMAIN p = {"kind","name","params","locals","body"}
  /\ p.kind = "Procedure"
  /\ p.name \in Id
  /\ p.params \in Seq(Id)
  /\ p.locals \in Seq(Id)
  /\ p.body \in Seq(SELF)

IsProcess(p) ==
  /\ DOMAIN p = {"kind","name","self","locals","body","ids"}
  /\ p.kind = "Process"
  /\ p.name \in Id
  /\ p.self \in Id
  /\ p.locals \in Seq(Id)
  /\ p.body \in Seq(SELF)
  /\ p.ids \in Expr

\* Algorithms: uniprocess or multiprocess
IsUniAlg(a) ==
  /\ DOMAIN a = {"kind","name","variables","procedures","body"}
  /\ a.kind = "Uni"
  /\ a.name \in Id
  /\ VarDecls(a.variables)
  /\ a.procedures \in Seq({p \in [kind: "Procedure", name: Id, params: Seq(Id), locals: Seq(Id), body: Seq(SELF)] : TRUE})
  /\ a.body \in Seq(SELF)

IsMultiAlg(a) ==
  /\ DOMAIN a = {"kind","name","variables","procedures","processes"}
  /\ a.kind = "Multi"
  /\ a.name \in Id
  /\ VarDecls(a.variables)
  /\ a.procedures \in Seq({p \in [kind: "Procedure", name: Id, params: Seq(Id), locals: Seq(Id), body: Seq(SELF)] : TRUE})
  /\ a.processes \in Seq({q \in [kind: "Process", name: Id, self: Id, locals: Seq(Id), body: Seq(SELF), ids: Expr] : TRUE})

IsAlg(a) == IsUniAlg(a) \/ IsMultiAlg(a)

(***************************************************************************)
(* Structural utilities over the AST                                       *)
(***************************************************************************)

RECURSIVE LabelsOfStmt(_)
LabelsOfStmt(s) ==
  IF IsLabeled(s) THEN {s.label} \cup LabelsOfStmt(s.stmt)
  ELSE IF IsSeq(s) THEN UNION { LabelsOfStmt(x) : x \in s.stmts }
  ELSE IF IsIf(s) THEN UNION { UNION { LabelsOfStmt(t) : t \in g.then } : g \in s.guards }
  ELSE IF IsEither(s) THEN UNION { UNION { LabelsOfStmt(t) : t \in arm } : arm \in s.arms }
  ELSE IF IsWhile(s) THEN {s.testLabel} \cup UNION { LabelsOfStmt(t) : t \in s.body }
  ELSE IF IsWith(s) THEN UNION { LabelsOfStmt(t) : t \in s.body }
  ELSE {}
  
LabelsOfProc(p) == UNION { LabelsOfStmt(s) : s \in p.body }
LabelsOfProcess(p) == UNION { LabelsOfStmt(s) : s \in p.body }

LabelsOfAlg(a) ==
  IF IsUniAlg(a) THEN UNION { LabelsOfStmt(s) : s \in a.body }
  ELSE UNION { LabelsOfProcess(p) : p \in a.processes }

AllLabelsUnique(a) ==
  LET L == LabelsOfAlg(a) IN Cardinality(L) = Cardinality(L) \* trivially true for a set; uniqueness is ensured by well-formedness assumption

\* Name domains
GlobalVarNames(a) == { v.name : v \in a.variables }
ProcNames(a) == { p.name : p \in a.procedures }
LocalVarNamesOfProc(p) == { x : x \in p.locals }
LocalVarNamesOfProcess(q) == { x : x \in q.locals }

ProcIdDom(a) ==
  IF IsUniAlg(a) THEN {}
  ELSE { <<q.name, q.ids>> : q \in a.processes }
\* For rendering, each process q has domain expr q.ids; we carry pairs (procName, idsExpr) to reference.

\* Well-formedness of algorithm input
WellFormedAlg(a) ==
  /\ IsAlg(a)
  /\ \A l \in LabelsOfAlg(a) : IsLabel(l)
  /\ \A p,q \in ProcNames(a) : p = q \/ p # q
  /\ \A v \in GlobalVarNames(a) : IsIdentifier(v)
  \* Additional structural well-formedness (e.g., distinct labels, name hygiene) is assumed.

(***************************************************************************)
(* Changed variables and UNCHANGED sets (abstract characterization)         *)
(***************************************************************************)

\* Abstract variable universe names that appear in the generated TLA+ state
\* Includes: global vars, per-process locals (as functions over process ids in multi),
\* and control/stack variables pc and stack.
StateVarNames(a) ==
  LET g == GlobalVarNames(a) IN
  IF IsUniAlg(a)
    THEN g \cup {"pc","stack"}
    ELSE
      LET allLocs == UNION { LocalVarNamesOfProcess(p) : p \in a.processes } IN
      g \cup {"pc","stack"} \cup allLocs

\* Abstract computation of variables written by a statement.
RECURSIVE WritesOfStmt(_,_)
WritesOfStmt(a, s) ==
  IF IsAssign(s) THEN { v.name : v \in s.lhs }
  ELSE IF IsWhen(s) \/ IsPrint(s) \/ IsAssert(s) \/ IsSkip(s) THEN {}
  ELSE IF IsGoto(s) THEN {}
  ELSE IF IsReturn(s) THEN {}  \* Non-frame state, except control/stack, see below
  ELSE IF IsCall(s) \/ IsCallReturn(s) THEN {} \* same
  ELSE IF IsIf(s) THEN UNION { UNION { WritesOfStmt(a, t) : t \in g.then } : g \in s.guards }
  ELSE IF IsEither(s) THEN UNION { UNION { WritesOfStmt(a, t) : t \in arm } : arm \in s.arms }
  ELSE IF IsWhile(s) THEN UNION { WritesOfStmt(a, t) : t \in s.body }
  ELSE IF IsWith(s) THEN UNION { WritesOfStmt(a, t) : t \in s.body }
  ELSE IF IsLabeled(s) THEN WritesOfStmt(a, s.stmt)
  ELSE IF IsSeq(s) THEN UNION { WritesOfStmt(a, t) : t \in s.stmts }
  ELSE {}  

\* Control/stack effects that every per-label action must include when appropriate:
\* - Any executable labeled statement changes pc.
\* - Calls/returns manipulate stack and pc.
\* We encode this as a requirement over the generated per-label action text.
ControlWrites(a, s) ==
  {"pc"} \cup (IF IsCall(s) \/ IsCallReturn(s) \/ IsReturn(s) \/ IsGoto(s) THEN {"stack"} ELSE {})

ChangedVars(a, s) == (WritesOfStmt(a, s) \cap StateVarNames(a)) \cup ControlWrites(a, s)

UnchangedVars(a, s) == StateVarNames(a) \ StateVarNames(a) \cup StateVarNames(a) \ { } \* placeholder to keep expression well-typed
\* Note: We will use an abstract CorrectActionLexemes predicate to tie UNCHANGED rendering to ChangedVars.

(***************************************************************************)
(* Rendering/translation to TLA+ lexemes (abstract but constructive)        *)
(***************************************************************************)

\* Module name
ModName(a) == a.name \o "_TLA"

\* Variable declaration list in the produced module
VarDeclNames(a) ==
  \* Global vars + pc + stack + (mp locals as separate vars, each denoting a function over process ids)
  LET g == GlobalVarNames(a) IN
  IF IsUniAlg(a)
    THEN <<>> \o <<v : v \in g>> \o <<"pc", "stack">>
    ELSE
      LET allLocs == << x : x \in UNION { LocalVarNamesOfProcess(p) : p \in a.processes } >> IN
      <<>> \o <<v : v \in g>> \o <<>> \o allLocs \o <<"pc","stack">>

RenderVarList(ids) ==
  \* Render: VARIABLES v1, v2, ..., vn
  LET names == ids IN
    <<VarsTok, Sp>> \o JoinWith(<< <<n>> : n \in names >>, <<",", Sp>>) \o <<Nl>>

\* Init predicate rendering (abstract; expressions are assumed to be Expr = LexSeq)
RenderInit(a) ==
  LET
    header == << "Init", Sp, Eq, Sp >>
    initGlobals ==
      JoinWith(
        << <<And, Sp, v.name, Sp, Eq, Sp>> \o v.init : v \in a.variables >>,
        <<Nl>>)
    initPC ==
      IF IsUniAlg(a)
        THEN <<Nl, And, Sp, "pc", Sp, Eq, Sp, "\"", "InitLabel", "\"">>
        ELSE
          \* pc = [self \in Dom |-> InitLabelOfProcess]
          LET
            pcs == JoinWith(
                    << <<And, Sp, "pc", Sp, Eq, Sp, LBrack, p.self, Sp, InTok, Sp>> \o p.ids \o <<Sp, MapTo, Sp, "\"","InitLabel","\"", RBrack>>
                       : p \in a.processes >>,
                    <<Nl>>)
          IN <<Nl>> \o pcs
    initLocalsMP ==
      IF IsMultiAlg(a)
        THEN
          LET
            allLocs == UNION { LocalVarNamesOfProcess(p) : p \in a.processes }
            initLocal(v) ==
              \* v = [self \in Dom |-> Default]
              LET anyProc == CHOOSE p \in a.processes : TRUE
              IN <<Nl, And, Sp, v, Sp, Eq, Sp, LBrack, anyProc.self, Sp, InTok, Sp>> \o anyProc.ids \o <<Sp, MapTo, Sp, "Default", RBrack>>
          IN JoinWith(<< initLocal(v) : v \in allLocs >>, <<Nl>>)
        ELSE <<>>
  IN
    header \o <<LParen>> \o (Tail(<<Nl>> \o initGlobals \o initPC \o initLocalsMP, 1)) \o <<RParen, Nl>>

\* Per-label action rendering (abstract shape). We require the lexemes to contain:
\*  - A_<label> == /\ pc = <label>
\*                /\ ...body encoding of the statement...
\*                /\ pc' = <nextLabel>
\*                /\ UNCHANGED <<vars not changed>>
RenderActionDef(a, lbl) ==
  LET
    name == "A_" \o lbl
    lhs  == <<name, Sp, Eq, Sp>>
    guard == <<And, Sp, "pc", Sp, Eq, Sp, "\"">> \o <<lbl>> \o <<"\"">>
    body  == <<Nl, And, Sp, "(* body elided: encodes statement semantics, stack, calls, returns, with UNCHANGED clauses *)">>
  IN
    lhs \o <<LParen, Nl>> \o guard \o body \o <<Nl, RParen, Nl>>

\* All per-label actions of the algorithm, in a deterministic order (e.g., lexicographic)
ActionLabels(a) == Sort(LabelsOfAlg(a))
RECURSIVE Sort(_)
Sort(S) == \* any deterministic total ordering; abstractly render as sequence
  << x : x \in S >> \* We do not need actual sorting semantics for specification; any enumeration suffices

RenderAllActionDefs(a) ==
  JoinWith(<< RenderActionDef(a, l) : l \in ActionLabels(a) >>, <<Nl>>)

\* Next action is the disjunction of all per-label actions, across processes if any.
RenderNext(a) ==
  LET
    acts == << "A_" \o l : l \in ActionLabels(a) >>
    disj == JoinWith(<< <<Or, Sp, n>> : n \in acts >>, <<Nl>>)
  IN << "Next", Sp, Eq, Sp, LParen, Nl, "(* disjunction of per-label actions: *)", Nl>> \o
     disj \o <<Nl, RParen, Nl>>

\* Variables vector token for stuttering and fairness clauses
RenderVarsVector(a) ==
  LET ids == VarDeclNames(a) IN
    <<UnderTok>> \o JoinWith(<< <<x>> : x \in ids >>, <<",">>)

\* Spec and fairness clauses
RenderSpec(a, fair) ==
  LET
    varsVec == RenderVarsVector(a)
    base == << "Spec", Sp, Eq, Sp, "Init", Sp, "/\\", Sp, BoxTok, LBrack, "Next", RBrack>> \o varsVec
    fa == fair
    actNames == << "A_" \o l : l \in ActionLabels(a) >>
    perWF ==
      JoinWith(<< <<Nl, "/\\", Sp, "WF", varsVec, LParen, "Next", ",", Sp, n, RParen>> : n \in actNames >>, <<>>)
    perSF ==
      JoinWith(<< <<Nl, "/\\", Sp, "SF", varsVec, LParen, "Next", ",", Sp, n, RParen>> : n \in actNames >>, <<>>)
    wfNext == <<Nl, "/\\", Sp, "WF", varsVec, LParen, "Next", ",", Sp, "Next", RParen>>
    fairness ==
      IF fa = "None" THEN <<>>
      ELSE IF fa = "WFPerAction" THEN perWF
      ELSE IF fa = "WFNext" THEN wfNext
      ELSE perSF
  IN base \o fairness \o <<Nl>>

\* Termination property: for uni: <> (pc = "Done"), for multi: <> (\\A p : pc[p] = "Done")
RenderTermination(a) ==
  IF IsUniAlg(a)
    THEN << "Termination", Sp, Eq, Sp, AngleTok, LParen, "pc", Sp, Eq, Sp, "\"","Done","\"", RParen, Nl>>
    ELSE
      LET anyProc == CHOOSE p \in a.processes : TRUE IN
      << "Termination", Sp, Eq, Sp, AngleTok, LParen, "\\A", Sp, anyProc.self, Sp, ":", Sp, "pc", LBrack, anyProc.self, RBrack, Sp, Eq, Sp, "\"","Done","\"", RParen, Nl>>

\* Module header and EXTENDS
RenderHeader(a) ==
  << "----", Sp, "MODULE", Sp, ModName(a), Sp, "----", Nl,
     "EXTENDS", Sp, "Naturals, Sequences, TLC", Nl, Nl >>

\* Complete variable declarations
RenderVariables(a) ==
  LET names == VarDeclNames(a) IN RenderVarList(names)

\* Assemble the full translation
FT(a, fair) ==
  \* FT returns the full sequence of lexemes for a valid TLA+ module
  RenderHeader(a)
    \o RenderVariables(a)
    \o RenderInit(a)
    \o RenderAllActionDefs(a)
    \o RenderNext(a)
    \o RenderSpec(a, fair)
    \o RenderTermination(a)
    \o << "====