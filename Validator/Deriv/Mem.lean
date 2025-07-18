import Validator.Deriv.MemEnter
import Validator.Deriv.MemLeave

class Mem (m: Type -> Type u) extends MemEnter.MemEnter m, MemLeave.MemLeave m
