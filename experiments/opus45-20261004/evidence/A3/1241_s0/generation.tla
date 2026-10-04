-------------------------------- MODULE PCalTranslator --------------------------------
(***************************************************************************)
(* This module specifies the translation from the abstract syntax tree of  *)
(* a global-naming PlusCal (+CAL) algorithm into a TLA+ specification.     *)
(* It defines the grammar of legal ASTs for algorithms, procedures,        *)
(* processes, and labeled statements, and operators that translate such    *)
(* trees into lexeme sequences representing TLA+ output.                   *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    \* AST Node Types
    AlgorithmNode,
    ProcedureNode,
    ProcessNode,
    LabeledStmtNode,
    AssignmentNode,
    IfNode,
    WhileNode,
    EitherNode,
    WithNode,
    CallNode,
    ReturnNode,
    GotoNode,
    PrintNode,
    AssertNode,
    SkipNode,
    AwaitNode,
    
    \* Fairness options for generated specification
    NoFairness,
    WeakFairnessOfProcessActions,
    WeakFairnessOfNext,
    StrongFairnessOfProcessActions,
    
    \* Special tokens/identifiers
    NullValue,
    
    \* Maximum bounds for model checking
    MaxProcesses,
    MaxProcedures,
    MaxLabels,
    MaxVars

VARIABLES
    \* The input AST being translated
    ast,
    
    \* Current state of translation
    translationState,
    
    \* Output lexeme sequence
    output,
    
    \* Symbol table for variables and procedures
    symbolTable,
    
    \* Current fairness setting
    fairnessOption,
    
    \* Error state
    errorState,
    
    \* Generated TLA+ components
    initPredicate,
    nextAction,
    specFormula,
    terminationProperty

vars == <<ast, translationState, output, symbolTable, fairnessOption, 
          errorState, initPredicate, nextAction, specFormula, terminationProperty>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type definitions and grammar for legal ASTs                             *)
(***************************************************************************)

\* Set of valid node types
NodeTypes == {AlgorithmNode, ProcedureNode, ProcessNode, LabeledStmtNode,
              AssignmentNode, IfNode, WhileNode, EitherNode, WithNode,
              CallNode, ReturnNode, GotoNode, PrintNode, AssertNode,
              SkipNode, AwaitNode}

\* Set of valid fairness options
FairnessOptions == {NoFairness, WeakFairnessOfProcessActions, 
                    WeakFairnessOfNext, StrongFairnessOfProcessActions}

\* A variable declaration record
IsVarDecl(v) == 
    /\ DOMAIN v = {"name", "initialValue"}
    /\ v.name \in STRING
    /\ v.initialValue \in STRING \cup {NullValue}

\* A labeled statement is well-formed
IsLabeledStmt(ls) ==
    /\ DOMAIN ls \subseteq {"type", "label", "statements", "fairness"}
    /\ ls.type = LabeledStmtNode
    /\ ls.label \in STRING
    /\ ls.statements \in Seq(STRING)

\* A procedure node is well-formed
IsProcedure(p) ==
    /\ DOMAIN p \subseteq {"type", "name", "params", "localVars", "body"}
    /\ p.type = ProcedureNode
    /\ p.name \in STRING

\* A process node is well-formed
IsProcess(pr) ==
    /\ DOMAIN pr \subseteq {"type", "name", "id", "localVars", "body", "fairness"}
    /\ pr.type = ProcessNode
    /\ pr.name \in STRING

\* An algorithm AST is well-formed
IsAlgorithm(a) ==
    /\ DOMAIN a \subseteq {"type", "name", "globalVars", "procedures", 
                           "processes", "fairness", "isMultiProcess"}
    /\ a.type = AlgorithmNode
    /\ a.name \in STRING

-----------------------------------------------------------------------------
(***************************************************************************)
(* Helper operators for building TLA+ lexeme sequences                     *)
(***************************************************************************)

\* Concatenate lexeme sequences
Concat(s1, s2) == s1 \o s2

\* Create a newline lexeme
Newline == <<"\n">>

\* Create an indentation lexeme
Indent(level) == 
    LET spaces == [i \in 1..level |-> "  "]
    IN <<Concat([i \in 1..level |-> "  ")>>

\* Wrap identifier
Ident(name) == <<name>>

\* Create operator definition
OpDef(name, params, body) ==
    Concat(Ident(name), 
    Concat(IF params = <<>> THEN <<>> ELSE Concat(<<"(">>, Concat(params, <<")">>)),
    Concat(<<" == ">>, body)))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Translation operators                                                   *)
(***************************************************************************)

\* Generate variable declarations for Init
TranslateVarDecl(v) ==
    IF v.initialValue = NullValue
    THEN Concat(Ident(v.name), <<" \\in {}">>)
    ELSE Concat(Ident(v.name), Concat(<<" = ">>, <<v.initialValue>>))

\* Generate conjunction of variable initializations
TranslateInit(globalVars, processes) ==
    LET varInits == [i \in 1..Len(globalVars) |-> TranslateVarDecl(globalVars[i])]
        pcInit == <<"pc = ", "[self \\in ProcSet |-> \"Init\"]">>
    IN Concat(<<"Init == ">>, 
       Concat(<<"/\\ ">>,
       Concat(IF Len(globalVars) > 0 THEN varInits[1] ELSE <<>>,
              pcInit)))

\* Generate action for a labeled statement
TranslateLabeledAction(procName, ls) ==
    LET actionName == Concat(Ident(procName), Concat(<<"_">>, Ident(ls.label)))
        pcGuard == Concat(<<"pc[self] = \"">>, Concat(<<ls.label>>, <<"\"">>))
    IN Concat(actionName, 
       Concat(<<"(self) == ">>,
       Concat(pcGuard, <<" /\\ TRUE">>)))

\* Generate Next action
TranslateNext(processes, procedures) ==
    Concat(<<"Next == ">>,
    Concat(<<"\\/ (\\E self \\in ProcSet: ">>,
           <<"TRUE)">>))

\* Generate fairness conditions
TranslateFairness(option, processes) ==
    CASE option = NoFairness -> <<>>
      [] option = WeakFairnessOfNext -> <<"WF_vars(Next)">>
      [] option = WeakFairnessOfProcessActions -> 
         <<"\\A self \\in ProcSet: WF_vars(proc(self))">>
      [] option = StrongFairnessOfProcessActions ->
         <<"\\A self \\in ProcSet: SF_vars(proc(self))">>
      [] OTHER -> <<>>

\* Generate Spec formula
TranslateSpec(initName, nextName, fairness) ==
    LET base == Concat(<<initName>>, Concat(<<" /\\ [][">>, 
                Concat(<<nextName>>, <<"]_vars">>)))
    IN IF fairness = <<>>
       THEN Concat(<<"Spec == ">>, base)
       ELSE Concat(<<"Spec == ">>, Concat(base, Concat(<<" /\\ ">>, fairness)))

\* Generate Termination property
TranslateTermination ==
    <<"Termination == <>(\\A self \\in ProcSet: pc[self] = \"Done\")">>

\* Main translation of algorithm AST
TranslateAlgorithm(alg) ==
    LET initDef == TranslateInit(alg.globalVars, alg.processes)
        nextDef == TranslateNext(alg.processes, alg.procedures)
        fairDef == TranslateFairness(alg.fairness, alg.processes)
        specDef == TranslateSpec("Init", "Next", fairDef)
        termDef == TranslateTermination
    IN Concat(initDef, 
       Concat(Newline,
       Concat(nextDef,
       Concat(Newline,
       Concat(specDef,
       Concat(Newline, termDef))))))

-----------------------------------------------------------------------------
(***************************************************************************)
(* State machine for translation process                                   *)
(***************************************************************************)

\* Translation states
TranslationStates == {"Idle", "Parsing", "Validating", "TranslatingInit",
                      "TranslatingNext", "TranslatingSpec", "Done", "Error"}

\* Initial state
Init ==
    /\ ast = [type |-> AlgorithmNode, 
              name |-> "default",
              globalVars |-> <<>>,
              procedures |-> <<>>,
              processes |-> <<>>,
              fairness |-> NoFairness,
              isMultiProcess |-> FALSE]
    /\ translationState = "Idle"
    /\ output = <<>>
    /\ symbolTable = [vars |-> {}, procs |-> {}, labels |-> {}]
    /\ fairnessOption = NoFairness
    /\ errorState = NullValue
    /\ initPredicate = <<>>
    /\ nextAction = <<>>
    /\ specFormula = <<>>
    /\ terminationProperty = <<>>

\* Start translation
StartTranslation ==
    /\ translationState = "Idle"
    /\ IsAlgorithm(ast)
    /\ translationState' = "Parsing"
    /\ UNCHANGED <<ast, output, symbolTable, fairnessOption, errorState,
                   initPredicate, nextAction, specFormula, terminationProperty>>

\* Validate AST
ValidateAST ==
    /\ translationState = "Parsing"
    /\ IF IsAlgorithm(ast)
       THEN /\ translationState' = "Validating"
            /\ errorState' = NullValue
       ELSE /\ translationState' = "Error"
            /\ errorState' = "Invalid AST structure"
    /\ UNCHANGED <<ast, output, symbolTable, fairnessOption,
                   initPredicate, nextAction, specFormula, terminationProperty>>

\* Build symbol table
BuildSymbolTable ==
    /\ translationState = "Validating"
    /\ symbolTable' = [vars |-> {v.name : v \in ToSet(ast.globalVars)},
                       procs |-> {p.name : p \in ToSet(ast.procedures)},
                       labels |-> {}]
    /\ translationState' = "TranslatingInit"
    /\ UNCHANGED <<ast, output, fairnessOption, errorState,
                   initPredicate, nextAction, specFormula, terminationProperty>>

\* Generate Init predicate
GenerateInit ==
    /\ translationState = "TranslatingInit"
    /\ initPredicate' = TranslateInit(ast.globalVars, ast.processes)
    /\ translationState' = "TranslatingNext"
    /\ UNCHANGED <<ast, output, symbolTable, fairnessOption, errorState,
                   nextAction, specFormula, terminationProperty>>

\* Generate Next action
GenerateNext ==
    /\ translationState = "TranslatingNext"
    /\ nextAction' = TranslateNext(ast.processes, ast.procedures)
    /\ translationState' = "TranslatingSpec"
    /\ UNCHANGED <<ast, output, symbolTable, fairnessOption, errorState,
                   initPredicate, specFormula, terminationProperty>>

\* Generate Spec and Termination
GenerateSpec ==
    /\ translationState = "TranslatingSpec"
    /\ LET fairDef == TranslateFairness(ast.fairness, ast.processes)
       IN /\ specFormula' = TranslateSpec("Init", "Next", fairDef)
          /\ terminationProperty' = TranslateTermination
    /\ output' = TranslateAlgorithm(ast)
    /\ translationState' = "Done"
    /\ UNCHANGED <<ast, symbolTable, fairnessOption, errorState,
                   initPredicate, nextAction>>

\* Set fairness option
SetFairness(f) ==
    /\ translationState = "Idle"
    /\ f \in FairnessOptions
    /\ fairnessOption' = f
    /\ ast' = [ast EXCEPT !.fairness = f]
    /\ UNCHANGED <<translationState, output, symbolTable, errorState,
                   initPredicate, nextAction, specFormula, terminationProperty>>

\* Load new AST
LoadAST(newAST) ==
    /\ translationState \in {"Idle", "Done", "Error"}
    /\ IsAlgorithm(newAST)
    /\ ast' = newAST
    /\ translationState' = "Idle"
    /\ output' = <<>>
    /\ errorState' = NullValue
    /\ UNCHANGED <<symbolTable, fairnessOption, initPredicate, 
                   nextAction, specFormula, terminationProperty>>

\* Next state relation
Next ==
    \/ StartTranslation
    \/ ValidateAST
    \/ BuildSymbolTable
    \/ GenerateInit
    \/ GenerateNext
    \/ GenerateSpec
    \/ \E f \in FairnessOptions : SetFairness(f)
    \/ \E a \in [type : {AlgorithmNode}, 
                 name : STRING,
                 globalVars : Seq([name : STRING, initialValue : STRING \cup {NullValue}]),
                 procedures : Seq([type : {ProcedureNode}, name : STRING]),
                 processes : Seq([type : {ProcessNode}, name : STRING]),
                 fairness : FairnessOptions,
                 isMultiProcess : BOOLEAN] : LoadAST(a)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Fairness conditions                                                     *)
(***************************************************************************)

\* Weak fairness of the translation process
Fairness == WF_vars(Next)

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

\* Translation state is always valid
TypeInvariant ==
    /\ translationState \in TranslationStates
    /\ fairnessOption \in FairnessOptions
    /\ output \in Seq(STRING)

\* If in Done state, output is non-empty
CompletionInvariant ==
    translationState = "Done" => Len(output) > 0

\* Error state is only set when in Error translation state
ErrorConsistency ==
    (errorState # NullValue) <=> (translationState = "Error")

\* Symbol table is consistent with AST
SymbolTableConsistency ==
    translationState \in {"TranslatingInit", "TranslatingNext", "TranslatingSpec", "Done"} =>
        symbolTable.vars = {v.name : v \in ToSet(ast.globalVars)}

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ CompletionInvariant

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* Translation eventually completes or errors
TranslationProgress ==
    (translationState = "Parsing") ~> (translationState \in {"Done", "Error"})

\* If AST is valid, translation eventually succeeds
TranslationSuccess ==
    (translationState = "Parsing" /\ IsAlgorithm(ast)) ~> (translationState = "Done")

\* Termination: system eventually reaches Done or Error state
Termination ==
    <>(translationState \in {"Idle", "Done", "Error"})

=============================================================================