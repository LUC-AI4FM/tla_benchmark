```
MODULE Outer
EXTENDS Integers, Sequences
CONSTANTS InnerSeq
VARIABLES inner_result, inner_sequence

Inner == INSTANCE InnerModule WITH result <- inner_result, sequence <- inner_sequence

Init ==
  /\ inner_result = 0
  /\ inner_sequence = <<>>

Next ==
  /\ (inner_result = 1) => UNCHANGED <<inner_result, inner_sequence>>
  /\ (inner_result = 0) => OR
    { Inner!Step
    , UNCHANGED <<inner_result, inner_sequence>> }

Spec == Init /\ [][Next]_<<inner_result, inner_sequence>>

THEOREM Spec => <>[]~(Enabled (<Inner!Step>_) )
```

 InnerModule.tla
```
MODULE InnerModule
EXTENDS Integers, Sequences
CONSTANTS Seq
VARIABLES result, sequence

Step ==
  /\ result' = 1
  /\ sequence' = SelectSeq(LAMBDA x : x # sequence : x /= result', sequence)

Init == result = 0 /\ sequence = <<>>

Next == Step \/ (UNCHANGED <<result, sequence>>)

Spec == Init /\ [][Next]_<<result, sequence>>
```