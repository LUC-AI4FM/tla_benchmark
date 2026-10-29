ffIndices : lo + i < length => buff[i] = LogicalAt(lo + i)

\* After a flush, the disk holds exactly the logical contents.
FlushPreservesLogical ==
    Resize(FlushedDisk, length) = LogicalContent

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract RandomAccessFile, written over the refinement mapping          *)
(***************************************************************************)

AbsContent == LogicalContent
AbsPointer == curr

absVars == <<AbsContent, AbsPointer>>

RAF_TypeOK ==
    /\ AbsContent \in ArrayOfAnyLength(SymbolOrArbitrary)
    /\ AbsPointer \in Offsets

RAF_Init ==
    /\ AbsContent \in ArrayOfAnyLength(Symbols)
    /\ AbsPointer = 0

RAF_Seek(pos) ==
    /\ pos \in Offsets
    /\ AbsPointer' = pos
    /\ UNCHANGED AbsContent

RAF_Read(sym) ==
    /\ AbsPointer < Len(AbsContent)
    /\ sym = AbsContent[AbsPointer + 1]
    /\ AbsPointer' = AbsPointer + 1
    /\ UNCHANGED AbsContent

RAF_Write(sym) ==
    /\ AbsPointer < MaxOffset
    /\ AbsContent' = WriteAt(AbsContent, AbsPointer, <<sym>>)
    /\ AbsPointer' = AbsPointer + 1

RAF_Flush == UNCHANGED <<AbsContent, AbsPointer>>

RAF_SetLength(n) ==
    /\ n \in Offsets
    /\ AbsContent' = Resize(AbsContent, n)
    /\ AbsPointer' = Min(AbsPointer, n)

RAF_Next ==
    \/ \E p \in Offsets : RAF_Seek(p)
    \/ \E s \in SymbolOrArbitrary : RAF_Read(s)
    \/ \E s \in Symbols : RAF_Write(s)
    \/ RAF_Flush
    \/ \E n \in Offsets : RAF_SetLength(n)

RAF_Spec == RAF_Init /\ [][RAF_Next]_absVars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement properties                                                   *)
(***************************************************************************)

\* The whole behavior refines the abstract RandomAccessFile.
Refinement == RAF_Spec

\* Each concrete operation refines its abstract counterpart.
SeekRefines ==
    [][\A p \in Offsets : Seek(p) => RAF_Seek(p)]_vars

ReadRefines ==
    [][\A s \in SymbolOrArbitrary : Read(s) => RAF_Read(s)]_vars

WriteRefines ==
    [][\A s \in Symbols : Write(s) => RAF_Write(s)]_vars

FlushRefines ==
    [][Flush => RAF_Flush]_vars

SetLengthRefines ==
    [][\A n \in Offsets : SetLength(n) => RAF_SetLength(n)]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking helpers                                                  *)
(***************************************************************************)

Symmetry == Permutations(Symbols)

Alias ==
    [ file_content    |-> file_content,
      disk_pos        |-> disk_pos,
      dirty           |-> dirty,
      length          |-> length,
      curr            |-> curr,
      lo              |-> lo,
      buff            |-> buff,
      logical_content |-> LogicalContent ]

=============================================================================

(***************************************************************************)
(* TLC configuration (BufferedRandomAccessFile.cfg)                        *)
(*                                                                         *)
(* CONSTANTS                                                               *)
(*     Symbols = {a, b}                                                    *)
(*     ArbitrarySymbol = ArbitrarySymbol                                   *)
(*     MaxOffset = 4                                                       *)
(*     BuffSize = 2                                                        *)
(*                                                                         *)
(* SPECIFICATION Spec                                                      *)
(* SYMMETRY Symmetry                                                       *)
(* ALIAS Alias                                                             *)
(*                                                                         *)
(* INVARIANTS                                                              *)
(*     TypeOK                                                              *)
(*     RAF_TypeOK                                                          *)
(*     LoAligned                                                           *)
(*     DiskNotLongerThanLogical                                            *)
(*     CleanMeansLengthsAgree                                              *)
(*     ExtensionWithinBuffer                                               *)
(*     DirtyBufferOverlapsFile                                             *)
(*     BufferBeyondEOFArbitrary                                            *)
(*     CleanBufferMatchesDisk                                              *)
(*     BufferMatchesLogical                                                *)
(*     FlushPreservesLogical                                               *)
(*                                                                         *)
(* PROPERTIES                                                              *)
(*     Refinement                                                          *)
(*     SeekRefines                                                         *)
(*     ReadRefines                                                         *)
(*     WriteRefines                                                        *)
(*     FlushRefines                                                        *)
(*     SetLengthRefines                                                    *)
(*                                                                         *)
(* Note: TLC may warn that SYMMETRY is unsound when checking temporal      *)
(* properties. Drop SYMMETRY to check the refinement properties soundly.   *)
(***************************************************************************)
```