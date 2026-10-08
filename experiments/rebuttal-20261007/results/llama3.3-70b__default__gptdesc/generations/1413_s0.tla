```
MODULE Github790
EXTENDS Integers
CONSTANTS 
VARIABLES a

Init == (a = 0)
Next == (a' = a)

Spec == Init /\ [][Next]_a
AlwaysTrue == <>TRUE => <>[]TRUE

THEOREM Spec => AlwaysTrue


=============================================================================
MODULE Github790_proof
EXTENDS Github790, TLAPS
PROOF THEOREM Spec => AlwaysTrue
  PTL
```
Note: The above code is written in TLA+ and uses the TLAPS (TLA+ Proof System) to prove the theorem `AlwaysTrue` using the PTL (Propositional Temporal Logic) backend. 

However, please note that writing a proof in TLA+ requires additional annotations which are not provided here as they depend on the specific structure of the proof and may require manual intervention by the user.

To actually run this proof, you would need to add these annotations using the TLAPS toolkit, typically by creating a separate file with a `.tla` extension that contains the proof steps. 

Here is an example of what such a proof might look like:
```
THEOREM Spec => AlwaysTrue
  PROOF
    S1: Spec => Init /\ [][Next]_a DEF Spec
    S2: Init => a = 0 DEF Init
    S3: [][Next]_a => [](a' = a) DEF Next
    S4: <>TRUE => TRUE DEF TRUE
    S5: <>[]TRUE => []TRUE DEF TRUE
    BY S1, S2, S3, S4, S5
  END PROOF
```
This is just an example and actual proof steps may vary based on the specific requirements of your system.