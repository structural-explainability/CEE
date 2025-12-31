namespace CEE.Core

abbrev ContextTagId := String
abbrev Uri := String

structure ContextTag where
  id : ContextTagId
  contextType : Option Uri := none
  label : Option String := none
  deriving Repr, BEq, DecidableEq

end CEE.Core
