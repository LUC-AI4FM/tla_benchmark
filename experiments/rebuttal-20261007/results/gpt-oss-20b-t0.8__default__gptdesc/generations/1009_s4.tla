MODULE BufferedFileSpec
EXTENDS Naturals, Sequences, TLC

CONSTANTS MaxBufferSize \in Nat, ArbitrarySymbol

VARIABLES buffer, pos, len, disk

(* ------------------------------------------------------------------
   Helper operator for element access with out-of-bounds returning
   ArbitrarySymbol. ----------------------------------------------- *)
Elem == [ seq, idx \in Seq(Symbol) |-> IF idx <= Len(seq)
                                        THEN SUBSEQ(seq, idx, idx)[1]
                                        ELSE ArbitrarySymbol ]

(* ------------------------------------------------------------------
   Invariants ------------------------------------------------------- *)
BufferBoundInv  == Len(buffer) <= MaxBufferSize
PositionInv     == 0 <= pos /\ pos <= len
LenDiskInv      == Len(disk) >= len

BufferMatchInv ==
  \A i \in 1..Len(buffer) :
    LET idx == pos + i IN
      IF idx <= len THEN
        Elem(buffer, i) = Elem(disk, idx)
      ELSE
        Elem(buffer, i) = ArbitrarySymbol

BufferInvariants == BufferBoundInv /\ PositionInv /\ LenDiskInv /\ BufferMatchInv

(* ------------------------------------------------------------------
   Initial state --------------------------------------------------- *)
Init ==
  buffer = <<>>
  /\ pos    = 0
  /\ len    = 0
  /\ disk   = <<>>

(* ------------------------------------------------------------------
   Actions --------------------------------------------------------- *)

SeekAction ==
  \E newPos \in 0..len :
    /\ buffer' = buffer
    /\ pos'    = newPos
    /\ len'    = len
    /\ disk'   = disk

ReadAction ==
  \E n \in 1..MaxBufferSize :
    LET endIdx == Min(len, pos + n) IN
    /\ buffer' = buffer
    /\ pos'    = endIdx
    /\ len'    = len
    /\ disk'   = disk

WriteAction ==
  \E data \in Seq(Symbol) :
    LET wlen       == Len(data)
        newBufLen  == Len(buffer)+wlen
    IN
      /\ newBufLen <= MaxBufferSize
      /\ buffer' = Append(buffer, data)
      /\ pos'    = pos
      /\ len'    = len
      /\ disk'   = disk

FlushAction ==
  \E :
    LET start     == pos
        endBuf    == start + Len(buffer)
        prefix    == IF start > 0 THEN SubSeq(disk,1,start-1) ELSE <<>>
        middle    == buffer
        suffixIdx == endBuf + 1
        suffix    == IF suffixIdx <= len THEN SubSeq(disk,suffixIdx,len) ELSE <<>>
        newDisk   == Append( Append(prefix,middle), suffix )
        newLen    == Max(len, endBuf)
    IN
      /\ disk' = newDisk
      /\ pos'  = endBuf
      /\ len'  = newLen
      /\ buffer'=<<>>

SetLengthAction ==
  \E newLen \in 0..Len(disk)+MaxBufferSize :
    LET newDisk == IF newLen < Len(disk)
                    THEN SubSeq(disk,1,newLen)
                    ELSE Append(disk,(ArbitrarySymbol :* (newLen - Len(disk))))
        finalPos== IF pos > newLen THEN newLen ELSE pos
    IN
      /\ disk' = newDisk
      /\ len'  = newLen
      /\ pos'  = finalPos
      /\ buffer'=<<>>

Next == SeekAction \/ ReadAction \/ WriteAction \/ FlushAction \/ SetLengthAction

(* ------------------------------------------------------------------
   Specification --------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ================================================================== *)

=============================================================================
CONSTANTS MaxBufferSize = 10, ArbitrarySymbol = "X"

SYMMETRY vars
ALIASING
INVARIANTS BufferInvariants
PROPERTIES Spec
=============================================================================

END BufferedFileSpec