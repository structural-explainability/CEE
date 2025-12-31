import EvolutionProtocol.Core.Base.Primitives

namespace CEE.Core.Base

abbrev VerifiableId := String
abbrev Uri :=
  EvolutionProtocol.Core.Base.Uri

inductive TargetKind where
  | aeEntity
  | epRecord
  | epGraphState
  | epGraphDelta
  | epGraphEvolution
  deriving Repr, BEq, DecidableEq

inductive TargetRef where
  | byVerifiableId (id : VerifiableId)
  | byUri (uri : Uri)
  | byDigest (alg : String) (hex : String)
  deriving Repr, BEq, DecidableEq

structure Target where
  kind : TargetKind
  ref : TargetRef
  deriving Repr, BEq, DecidableEq

structure Attachment where
  targets : List Target
  deriving Repr, BEq, DecidableEq

def Attachment.Nonempty (a : Attachment) : Prop :=
  a.targets ≠ []

end CEE.Core.Base
