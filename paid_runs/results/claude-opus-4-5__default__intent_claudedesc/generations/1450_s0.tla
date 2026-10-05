---------------------------- MODULE RandomFunctionSample ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    DomainSize,     \* Should be around 9
    CodomainMax,    \* Should be around 10
    SampleSize      \* Should be around 1000

VARIABLES
    sampledFunctions

\* Define the domain as a set of integers from 1 to DomainSize
Domain == 1..DomainSize

\* Define the codomain as a set of integers from 1 to CodomainMax
Codomain == 1..CodomainMax

\* The full set of functions from Domain to Codomain
\* For DomainSize=9 and CodomainMax=10, this has 10^9 elements
AllFunctions == [Domain -> Codomain]

\* Initialize by randomly sampling approximately SampleSize functions
\* from the astronomically large function space
Init ==
    sampledFunctions = RandomSubset(SampleSize, AllFunctions)

\* The system remains static after initialization
\* No transitions occur - this is a demonstration of RandomSubset capability
Next ==
    UNCHANGED sampledFunctions

\* The complete specification with no fairness requirements
\* since we only care about the initial sampling demonstration
Spec == Init /\ [][Next]_sampledFunctions

\* Trivially true invariant - the purpose is to demonstrate that
\* RandomSubset can efficiently sample from a 10^9 element function space
\* without timing out or attempting full enumeration
TrivialInvariant == TRUE

\* Additional invariant to verify the sample was actually created
\* and has reasonable size (may be slightly less than SampleSize due to randomness)
SampleExists == sampledFunctions # {}

\* Verify that all sampled elements are indeed functions with correct signature
AllAreFunctions == \A f \in sampledFunctions : 
                      DOMAIN f = Domain /\ \A x \in Domain : f[x] \in Codomain

\* Combined type invariant
TypeInvariant == 
    /\ sampledFunctions \subseteq AllFunctions
    /\ Cardinality(sampledFunctions) <= SampleSize

===================================================================================