import CEE.Core.Base.Refs

namespace CEE.Core

abbrev AttestationId := String

structure Attestation where
  attestationId : AttestationId
  attests : Base.Attachment
  attestorRef : Option String := none
  assertedAt : Option String := none
  deriving Repr, BEq, DecidableEq

end CEE.Core
