---------------------------- MODULE ProceduralComposition ----------------------------
EXTENDS Integers, Strings

CONSTANT defaultInitValue

VARIABLE return_value, output, pc

ProcAdd(a, b) {
  return_value := a + b;
}

ProcConvertToString(n) {
  IF n = 10 THEN
    return_value := "10";
  ENDIF;
}

Spec == 
  /\ pc = "Start"
  /\ [][
      (pc = "Start") => 
        ( 
          ProcAdd(3, 7);
          pc := "Added";
          assert return_value = 10;
        )
      \/ (pc = "Added") => 
        ( 
          ProcConvertToString(return_value);
          output := return_value;
          pc := "Done";
          assert output = "10";
        )
      \/ (pc = "Done") => UNCHANGED <<pc, return_value, output>>
    ]
  /\ <>[](pc = "Done")

defaultInitValue == << "Start", 0, "" >>
=============================================================================