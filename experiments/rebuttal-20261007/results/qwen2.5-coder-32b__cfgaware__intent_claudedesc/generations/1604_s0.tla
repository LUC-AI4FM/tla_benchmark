------------------------------- MODULE ProcComp -------------------------------

CONSTANTS
    defaultInitValue \* This constant must be defined

VARIABLES 
    sumResult, strResult, output

\* Define procedures with shared variables to simulate return values
PROCEDURE Add(IN x \in Int, IN y \in Int)
BEGIN
    sumResult := x + y;
END PROCEDURE;

PROCEDURE ConvertToString(IN num \in Int)
BEGIN
    IF num = 10 THEN
        strResult := "10";
    ELSE
        strResult := "?"; \* Undefined behavior for other numbers, as per problem statement
    ENDIF;
END PROCEDURE;

\* Main process logic
PROCESS ProcCompProcess =
BEGIN
    sumResult := defaultInitValue;
    strResult := defaultInitValue;
    output := defaultInitValue;
    
    CALL Add(3, 7);
    ASSERT sumResult = 10; \* Check that the addition result is correct
    
    CALL ConvertToString(sumResult);
    ASSERT strResult = "10"; \* Check that the conversion result is correct
    
    output := strResult;
    ASSERT output = "10"; \* Final assertion to check the output
END PROCESS;

\* Specification definition
Spec ==
    /\ PCInit(ProcCompProcess)
    /\ [][Next]_<<sumResult, strResult, output>>
    /\ WF_next(<<sumResult, strResult, output>>)

\* Liveness property: the process must eventually reach a completed state
Completed == output = "10"
Termination == <>[]<>[Completed]_<<sumResult, strResult, output>>

===============================================================================