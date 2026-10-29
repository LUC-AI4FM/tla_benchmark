```tla
]
    /\ file_content \in ArrayOfAnyLength(SymbolOrArbitrary)
    /\ last_read \in ArrayOfAnyLength(SymbolOrArbitrary)

\* The file pointer always lies within (or just past) the buffer window.
CurrInBuffer == lo <= curr /\ curr <= lo + BuffSz

\* The disk is never longer than the logical file.
DiskNotLongerThanLength == Len(file_content) <= length

\* A clean buffer means that disk and logical contents agree exactly.
CleanMeansSynced == ~dirty => LogicalFileContents = file_content

\* The logical file can extend past the disk only through dirty buffer data.
ExtensionOnlyInBuffer ==
    Len(file_content) < length =>
        /\ dirty
        /\ lo < length
        /\ length <= lo + BuffSz

\* Buffer slots past the logical end of the file hold unspecified contents.
BuffBeyondLengthArbitrary ==
    \A i \in 1..BuffSz : lo + i > length => buff[i] = ArbitrarySymbol

\* When the buffer is clean, every buffered slot agrees with the disk.
BufferCoherentWhenClean ==
    ~dirty =>
        \A i \in 1..BuffSz :
            lo + i <= Len(file_content) => buff[i] = file_content[lo + i]

LengthMatchesLogical == Len(LogicalFileContents) = length

Invariants ==
    /\ TypeOK
    /\ CurrInBuffer
    /\ DiskNotLongerThanLength
    /\ CleanMeansSynced
    /\ ExtensionOnlyInBuffer
    /\ BuffBeyondLengthArbitrary
    /\ BufferCoherentWhenClean
    /\ LengthMatchesLogical

(***************************************************************************)
(* ----------------------- Refinement properties ------------------------- *)
(***************************************************************************)
\* The whole behavior refines the abstract RandomAccessFile spec.
Refinement == AbsSpec

THEOREM Spec => Refinement

\* Each concrete operation refines its abstract counterpart.
SeekRefines      == [][(\E pos \in Offset : Seek(pos)) => AbsSeek]_vars
ReadRefines      == [][Read => AbsRead(last_read')]_vars
WriteRefines     == [][(\E s \in Symbols : Write(s)) => AbsWrite]_vars
FlushRefines     == [][Flush => AbsFlush]_vars
SetLengthRefines == [][(\E n \in Offset : SetLength(n)) => AbsSetLength]_vars

THEOREM Spec => /\ SeekRefines
                /\ ReadRefines
                /\ WriteRefines
                /\ FlushRefines
                /\ SetLengthRefines

(***************************************************************************)
(* ----------------------- Model-checking helpers ------------------------ *)
(***************************************************************************)
Symmetry == Permutations(Symbols)

Alias ==
    [ dirty        |-> dirty,
      length       |-> length,
      curr         |-> curr,
      lo           |-> lo,
      buff         |-> buff,
      diskPos      |-> diskPos,
      file_content |-> file_content,
      last_read    |-> last_read,
      logical      |-> LogicalFileContents,
      abs_pointer  |-> AbsPointer ]

(***************************************************************************)
(* TLC configuration (BufferedRandomAccessFile.cfg):                       *)
(*                                                                         *)
(*   CONSTANTS                                                             *)
(*       Symbols = {s1, s2}                                                *)
(*       ArbitrarySymbol = ArbitrarySymbol                                 *)
(*       MaxOffset = 3                                                     *)
(*       BuffSz = 2                                                        *)
(*   SPECIFICATION Spec                                                    *)
(*   SYMMETRY Symmetry                                                     *)
(*   ALIAS Alias                                                           *)
(*   INVARIANTS                                                            *)
(*       TypeOK                                                            *)
(*       CurrInBuffer                                                      *)
(*       DiskNotLongerThanLength                                           *)
(*       CleanMeansSynced                                                  *)
(*       ExtensionOnlyInBuffer                                             *)
(*       BuffBeyondLengthArbitrary                                         *)
(*       BufferCoherentWhenClean                                           *)
(*       LengthMatchesLogical                                              *)
(*   PROPERTIES                                                            *)
(*       Refinement                                                        *)
(*       SeekRefines                                                       *)
(*       ReadRefines                                                       *)
(*       WriteRefines                                                      *)
(*       FlushRefines                                                      *)
(*       SetLengthRefines                                                  *)
(*                                                                         *)
(* Here s1, s2 and ArbitrarySymbol are model values.                       *)
(***************************************************************************)
=============================================================================
```