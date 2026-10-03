---- MODULE BufferedRAF ----
EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* This specification models a buffered random-access file implementation. *)
(* It defines the concrete state (buffer, disk, pointers) and operations   *)
(* (seek, read, write, flush, setLength). It also includes an abstract     *)
(* specification of a random-access file and verifies that the concrete    *)
(* implementation refines the abstract one.                                *)
(***************************************************************************)

CONSTANTS
    \* Model value constants
    Data,              \* The set of possible byte values.
    ArbitrarySymbol,   \* A special symbol for uninitialized data.
    
    \* Model size constants for TLC
    BufferSize,        \* The size of the in-memory buffer.
    MaxFileLength,     \* The maximum logical length of the file.
    MaxWriteLength,    \* The maximum number of bytes in a single write.
    MaxReadLength      \* The maximum number of bytes in a single read.

ASSUME ArbitrarySymbol \notin Data
ASSUME BufferSize > 0
ASSUME MaxFileLength >= 0
ASSUME MaxWriteLength > 0
ASSUME MaxReadLength > 0

-----------------------------------------------------------------------------
(* UTILITIES *)

Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

\* Fill a sequence of length `len` with value `val`.
SeqFill(len, val) == [i \in 1..len |-> val]

\* Overwrite a subsequence of `seq` starting at 1-based `offset` with `sub`.
Overwrite(seq, offset, sub) ==
    [i \in DOMAIN seq |-> IF i >= offset /\ i < offset + Len(sub)
                          THEN sub[i - offset + 1]
                          ELSE seq[i]]

=============================================================================