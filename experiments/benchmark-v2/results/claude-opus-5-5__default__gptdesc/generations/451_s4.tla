------------------------------ MODULE ParamInstance ------------------------------
(***************************************************************************)
(* Test specification for parametrized INSTANCE usage. It is not a model *)
(* of a full algorithm. It checks how JSpec (an instance with an explicit *)
(* substitution) is handled compared with ISpec (a parametrized instance, *)
(* where the substitution comes from the operator argument).              *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE y

    ---------------------------- MODULE Inner ----------------------------
    EXTENDS Naturals

    VARIABLE x

    InnerInit == x = 0

    InnerNext == x' = (x + 1) % 5

    Spec == InnerInit /\ [][InnerNext]_x
    ======================================================================