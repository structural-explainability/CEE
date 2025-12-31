import CEE.Core.Base.Refs
import CEE.Core.ContextTag

namespace CEE.Core

abbrev ExplanationId := String


structure ExplanationRecord where
  explanationId : ExplanationId
  attachesTo : Base.Attachment
  contextTags : List ContextTagId := []
  contentType : Option Uri := none
  contentRef : Option String := none
  deriving Repr, BEq, DecidableEq

def ExplanationRecord.WellFormed (r : ExplanationRecord) : Prop :=
  r.attachesTo.targets ≠ []

end CEE.Core
