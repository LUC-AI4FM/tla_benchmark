---- MODULE OldPlusCal ----

CONSTANTS ast, fairness

VARIABLES pc, stack, vars

(*--algorithm OldPlusCal
variables pc = << >>,
          stack = << >>,
          vars = {}

fairness ""

begin

Translation ==
    LET 
        FullyExplodeSeq(seq) == seq
        Explode(stmt) == stmt
        AddSubscripts(vars, procId) == { v :<< procId, v >> : v \in vars }
        TranslateProcedures(alg) == alg
        TranslateCallsReturnsGotos(alg) == alg
        GenerateInit(alg) == "Init"
        GenerateNext(alg) == "Next"
        GenerateSpec(alg) == "Spec"
        GenerateProcSet(alg) == "ProcSet"
        GenerateVars(alg) == "vars"
        GenerateTermination(alg) == "Termination"
        AppendFairness(spec, fairnessOption) ==
            IF fairnessOption = "" THEN spec
            ELSE IF fairnessOption = "wf" THEN spec \o "WF_<< >>"
            ELSE IF fairnessOption = "wfNext" THEN spec \o "WF_next"
            ELSE IF fairnessOption = "sf" THEN spec \o "SF_<< >>"
    IN AppendFairness(
        GenerateInit(alg) \o
        GenerateNext(alg) \o
        GenerateSpec(alg) \o
        GenerateProcSet(alg) \o
        GenerateVars(alg) \o
        GenerateTermination(alg),
        fairness)

ASSUME << Translation(ast, fairness) >>

end algorithm;*)

Object == INSTANCE OldPlusCal

Any == BOOLEAN

====