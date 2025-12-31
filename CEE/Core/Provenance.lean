import CEE.Core.Base.Refs

namespace CEE.Core

abbrev ProvenanceId := String

structure ProvenanceRecord where
  provenanceId : ProvenanceId
  appliesTo : Base.Attachment
  method : Option String := none
  agentRef : Option String := none
  generatedAt : Option String := none
  deriving Repr, BEq, DecidableEq

end CEE.Core
