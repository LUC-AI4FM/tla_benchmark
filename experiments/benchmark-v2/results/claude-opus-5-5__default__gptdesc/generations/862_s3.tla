-------------------------------- MODULE MC --------------------------------
(***************************************************************************)
(* Model-checking parameterization module for the SPA_Attack_New system.   *)
(* It supplies concrete values for the network configuration constants     *)
(* (IP addresses, ports, flags and identifiers for the attacker and        *)
(* client configurations). It defines no protocol behavior of its own.     *)
(* The Init/Next/Spec below hold the configuration fixed so the module     *)
(* parses on its own. When SPA_Attack_New is available, replace the        *)
(* EXTENDS line with "EXTENDS SPA_Attack_New, TLC" and bind each constant  *)
(* to the matching const_* definition in the .cfg file.                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    SERVER_IP,          \* IP address of the SPA-protected server
    CLIENT_IP,          \* IP address of the legitimate client
    ATTACKER_IP,        \* IP address used by the attacker
    SPA_PORT,           \* UDP port on which SPA knock packets are sent
    SERVICE_PORT,       \* protected service port opened after a valid knock
    CLIENT_SRC_PORT,    \* client source port
    ATTACKER_SRC_PORT,  \* attacker source port
    SYN_FLAG,           \* TCP flag identifiers
    ACK_FLAG,
    SYNACK_FLAG,
    RST_FLAG,
    CLIENT_ID,          \* identifier of the client configuration
    ATTACKER_ID         \* identifier of the attacker configuration

---------------------------------------------------------------------------
(* Concrete constant values used by TLC *)

const_SERVER_IP         == "10.0.0.1"
const_CLIENT_IP         == "10.0.0.2"
const_ATTACKER_IP       == "10.0.0.66"
const_SPA_PORT          == 62201
const_SERVICE_PORT      == 22
const_CLIENT_SRC_PORT   == 40000
const_ATTACKER_SRC_PORT == 40001
const_SYN_FLAG          == "SYN"
const_ACK_FLAG          == "ACK"
const_SYNACK_FLAG       == "SYNACK"
const_RST_FLAG          == "RST"
const_CLIENT_ID         == "client"
const_ATTACKER_ID       == "attacker"

---------------------------------------------------------------------------
(* Check that the supplied constant values are well-formed *)

Flags == {SYN_FLAG, ACK_FLAG, SYNACK_FLAG, RST_FLAG}

ConstantsOK ==
    /\ SPA_PORT \in Nat
    /\ SERVICE_PORT \in Nat
    /\ CLIENT_SRC_PORT \in Nat
    /\ ATTACKER_SRC_PORT \in Nat
    /\ SPA_PORT # SERVICE_PORT
    /\ CLIENT_IP # ATTACKER_IP
    /\ CLIENT_ID # ATTACKER_ID
    /\ Cardinality(Flags) = 4

ASSUME ConstantsOK

---------------------------------------------------------------------------
(* Placeholder state so the module is complete on its own. *)
(* The configuration is written once and never changes.    *)

VARIABLE config

ConfigRecord ==
    [ serverIP        |-> SERVER_IP,
      clientIP        |-> CLIENT_IP,
      attackerIP      |-> ATTACKER_IP,
      spaPort         |-> SPA_PORT,
      servicePort     |-> SERVICE_PORT,
      clientSrcPort   |-> CLIENT_SRC_PORT,
      attackerSrcPort |-> ATTACKER_SRC_PORT,
      flags           |-> Flags,
      clientId        |-> CLIENT_ID,
      attackerId      |-> ATTACKER_ID ]

Init == config = ConfigRecord

Next == UNCHANGED config

Spec == Init /\ [][Next]_config

(* Safety: the configuration never changes *)
ConfigInvariant == config = ConfigRecord

THEOREM Spec => []ConfigInvariant
===========================================================================