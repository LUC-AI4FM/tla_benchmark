------------------------------- MODULE MC -------------------------------
(***************************************************************************)
(* Model-checking configuration module for SPA_Attack_New.                 *)
(* Supplies concrete values for the network configuration constants:       *)
(* IP addresses, ports, flags, and identifiers for the attacker and        *)
(* client configurations. It defines no protocol behavior of its own.      *)
(* SPA_Attack_New is not available here, so this module is written to be   *)
(* self-contained and parse on its own. The constant declarations below    *)
(* stand in for those of SPA_Attack_New. The behavior is a trivial         *)
(* stuttering spec over a single bookkeeping variable, so that the module  *)
(* has well-formed Init/Next/Spec.                                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    SPA_SERVER_IP,          \* IP address of the SPA-protected server
    SPA_SERVER_PORT,        \* Port the SPA server listens on
    SERVICE_PORT,           \* Port of the protected service
    CLIENT_IP,              \* IP address of the legitimate client
    CLIENT_PORT,            \* Source port of the legitimate client
    CLIENT_ID,              \* Identifier of the legitimate client
    ATTACKER_IP,            \* IP address of the attacker
    ATTACKER_PORT,          \* Source port of the attacker
    ATTACKER_ID,            \* Identifier of the attacker
    SYN_FLAG,               \* TCP SYN flag value
    ACK_FLAG,               \* TCP ACK flag value
    RST_FLAG,               \* TCP RST flag value
    FIN_FLAG,               \* TCP FIN flag value
    SPA_FLAG                \* Flag marking an SPA knock packet

(***************************************************************************)
(* Concrete constant definitions (Toolbox-style "const_" operators).       *)
(* In the .cfg file each CONSTANT is bound with "<-" to its definition.    *)
(***************************************************************************)
const_SPA_SERVER_IP   == "10.0.0.1"
const_SPA_SERVER_PORT == 62201
const_SERVICE_PORT    == 22
const_CLIENT_IP       == "10.0.0.2"
const_CLIENT_PORT     == 40000
const_CLIENT_ID       == "client"
const_ATTACKER_IP     == "10.0.0.66"
const_ATTACKER_PORT   == 50000
const_ATTACKER_ID     == "attacker"
const_SYN_FLAG        == "SYN"
const_ACK_FLAG        == "ACK"
const_RST_FLAG        == "RST"
const_FIN_FLAG        == "FIN"
const_SPA_FLAG        == "SPA"

(***************************************************************************)
(* Aggregated configuration records.                                       *)
(***************************************************************************)
ServerConfig ==
    [ ip |-> SPA_SERVER_IP, spaPort |-> SPA_SERVER_PORT,
      servicePort |-> SERVICE_PORT ]

ClientConfig ==
    [ id |-> CLIENT_ID, ip |-> CLIENT_IP, port |-> CLIENT_PORT ]

AttackerConfig ==
    [ id |-> ATTACKER_ID, ip |-> ATTACKER_IP, port |-> ATTACKER_PORT ]

Flags == { SYN_FLAG, ACK_FLAG, RST_FLAG, FIN_FLAG, SPA_FLAG }

Ports == { SPA_SERVER_PORT, SERVICE_PORT, CLIENT_PORT, ATTACKER_PORT }

(***************************************************************************)
(* Assumptions on the supplied parameters.                                 *)
(***************************************************************************)
ASSUME ConstantsWellFormed ==
    /\ Ports \subseteq 0..65535
    /\ CLIENT_IP # ATTACKER_IP
    /\ CLIENT_ID # ATTACKER_ID
    /\ SPA_SERVER_IP \notin { CLIENT_IP, ATTACKER_IP }
    /\ Cardinality(Flags) = 5

(***************************************************************************)
(* Trivial behavior. The module has no protocol behavior of its own.       *)
(***************************************************************************)
VARIABLES config

vars == << config >>

Init ==
    config = [ server   |-> ServerConfig,
               client   |-> ClientConfig,
               attacker |-> AttackerConfig,
               flags    |-> Flags ]

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants: the configuration stays fixed and well formed.              *)
(***************************************************************************)
TypeOK ==
    /\ config.server.spaPort \in 0..65535
    /\ config.server.servicePort \in 0..65535
    /\ config.client.port \in 0..65535
    /\ config.attacker.port \in 0..65535
    /\ config.flags = Flags

ConfigConstant ==
    config = [ server   |-> ServerConfig,
               client   |-> ClientConfig,
               attacker |-> AttackerConfig,
               flags    |-> Flags ]

AttackerDistinctFromClient ==
    /\ config.attacker.ip # config.client.ip
    /\ config.attacker.id # config.client.id

THEOREM Spec => [](TypeOK /\ ConfigConstant /\ AttackerDistinctFromClient)
=============================================================================