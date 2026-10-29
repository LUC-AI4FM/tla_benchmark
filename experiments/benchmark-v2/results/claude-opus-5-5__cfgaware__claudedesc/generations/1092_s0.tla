------------------------------ MODULE product ------------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

VARIABLES tee, stage, cycle, primer, product,
          longTemplate, shortTemplate, tinyTemplate,
          longHybrid, shortHybrid, tinyHybrid,
          longLongDouble, shortLongDouble, tinyShortDouble

vars == << tee, stage, cycle, primer, product,
           longTemplate, shortTemplate, tinyTemplate,
           longHybrid, shortHybrid, tinyHybrid,
           longLongDouble, shortLongDouble, tinyShortDouble >>

natMin(a, b) == IF a < b THEN a ELSE b

AnnealAmounts(p, t) == IF natMin(p, t) > 0 THEN 1..natMin(p, t) ELSE {0}

-----------------------------------------------------------------------------
(* Refinement mapping to the coarser "stages" abstraction *)
sDna      == longLongDouble + shortLongDouble + tinyShortDouble + product
sTemplate == longTemplate + shortTemplate + tinyTemplate
sHybrid   == longHybrid + shortHybrid + tinyHybrid

-----------------------------------------------------------------------------
TypeOK ==
    /\ tee \in {"Hot", "TooHot", "Warm"}
    /\ stage \in {"extended", "cooled", "annealed"}
    /\ cycle \in Nat
    /\ primer \in Nat
    /\ product \in Nat
    /\ longTemplate \in Nat
    /\ shortTemplate \in Nat
    /\ tinyTemplate \in Nat
    /\ longHybrid \in Nat
    /\ shortHybrid \in Nat
    /\ tinyHybrid \in Nat
    /\ longLongDouble \in Nat
    /\ shortLongDouble \in Nat
    /\ tinyShortDouble \in Nat

Init ==
    /\ tee = "Hot"
    /\ stage = "extended"
    /\ cycle = 0
    /\ primer = PRIMER
    /\ product = 0
    /\ longTemplate = 0
    /\ shortTemplate = 0
    /\ tinyTemplate = 0
    /\ longHybrid = 0
    /\ shortHybrid = 0
    /\ tinyHybrid = 0
    /\ longLongDouble = DNA
    /\ shortLongDouble = 0
    /\ tinyShortDouble = 0

heat ==
    /\ tee = "Hot"
    /\ stage = "extended"
    /\ tee' = "TooHot"
    /\ stage' = "extended"
    /\ primer' = primer + longHybrid + shortHybrid + tinyHybrid
    /\ longTemplate' = longTemplate + longHybrid + 2 * longLongDouble + shortLongDouble
    /\ shortTemplate' = shortTemplate + shortHybrid + shortLongDouble + tinyShortDouble
    /\ tinyTemplate' = tinyTemplate + tinyHybrid + tinyShortDouble + 2 * product
    /\ longHybrid' = 0
    /\ shortHybrid' = 0
    /\ tinyHybrid' = 0
    /\ longLongDouble' = 0
    /\ shortLongDouble' = 0
    /\ tinyShortDouble' = 0
    /\ product' = 0
    /\ UNCHANGED cycle

cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ stage' = "cooled"
    /\ UNCHANGED << cycle, primer, product,
                    longTemplate, shortTemplate, tinyTemplate,
                    longHybrid, shortHybrid, tinyHybrid,
                    longLongDouble, shortLongDouble, tinyShortDouble >>

anneal ==
    /\ tee = "Hot"
    /\ stage = "cooled"
    /\ tee' = "Warm"
    /\ stage' = "annealed"
    /\ \E kl \in 0..longTemplate, ks \in 0..shortTemplate, kt \in 0..tinyTemplate :
         /\ kl + ks + kt \in AnnealAmounts(primer, longTemplate + shortTemplate + tinyTemplate)
         /\ primer' = primer - (kl + ks + kt)
         /\ longTemplate' = longTemplate - kl
         /\ shortTemplate' = shortTemplate - ks
         /\ tinyTemplate' = tinyTemplate - kt
         /\ longHybrid' = longHybrid + kl
         /\ shortHybrid' = shortHybrid + ks
         /\ tinyHybrid' = tinyHybrid + kt
    /\ UNCHANGED << cycle, product, longLongDouble, shortLongDouble, tinyShortDouble >>

extend ==
    /\ tee = "Warm"
    /\ stage = "annealed"
    /\ tee' = "Hot"
    /\ stage' = "extended"
    /\ cycle' = cycle + 1
    /\ shortLongDouble' = shortLongDouble + longHybrid
    /\ tinyShortDouble' = tinyShortDouble + shortHybrid
    /\ product' = product + tinyHybrid
    /\ longHybrid' = 0
    /\ shortHybrid' = 0
    /\ tinyHybrid' = 0
    /\ UNCHANGED << primer, longTemplate, shortTemplate, tinyTemplate, longLongDouble >>

Next == heat \/ cool \/ anneal \/ extend

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(heat)
        /\ WF_vars(cool)
        /\ WF_vars(anneal)
        /\ WF_vars(extend)

thirdCycleProduct == (cycle < 3) => (product = 0)

-----------------------------------------------------------------------------
(* The coarser "stages" abstraction, instantiated via the refinement mapping *)

svars == << tee, stage, primer, sDna, sTemplate, sHybrid >>

SInit ==
    /\ tee = "Hot"
    /\ stage = "extended"
    /\ primer = PRIMER
    /\ sDna = DNA
    /\ sTemplate = 0
    /\ sHybrid = 0

SHeat ==
    /\ tee = "Hot"
    /\ stage = "extended"
    /\ tee' = "TooHot"
    /\ stage' = "extended"
    /\ primer' = primer + sHybrid
    /\ sTemplate' = sTemplate + sHybrid + 2 * sDna
    /\ sDna' = 0
    /\ sHybrid' = 0

SCool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ stage' = "cooled"
    /\ primer' = primer
    /\ sDna' = sDna
    /\ sTemplate' = sTemplate
    /\ sHybrid' = sHybrid

SAnneal ==
    /\ tee = "Hot"
    /\ stage = "cooled"
    /\ tee' = "Warm"
    /\ stage' = "annealed"
    /\ sDna' = sDna
    /\ \E k \in AnnealAmounts(primer, sTemplate) :
         /\ primer' = primer - k
         /\ sTemplate' = sTemplate - k
         /\ sHybrid' = sHybrid + k

SExtend ==
    /\ tee = "Warm"
    /\ stage = "annealed"
    /\ tee' = "Hot"
    /\ stage' = "extended"
    /\ primer' = primer
    /\ sTemplate' = sTemplate
    /\ sDna' = sDna + sHybrid
    /\ sHybrid' = 0

SNext == SHeat \/ SCool \/ SAnneal \/ SExtend

stagesSpec == /\ SInit
              /\ [][SNext]_svars
              /\ WF_svars(SHeat)
              /\ WF_svars(SCool)
              /\ WF_svars(SAnneal)
              /\ WF_svars(SExtend)

primerDepleted == <>(primer = 0)

=============================================================================