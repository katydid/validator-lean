-- TODO: consider a more flexible Predicate model, for example:
-- https://github.com/katydid/regex-deriv-lean/blob/main/RegexDeriv/Regex/Predicate.lean
-- First definitions in regex-deriv-lean to use LawfulOrd

inductive Pred (α: Type) where
  | eq (t: α)
  | any
  deriving DecidableEq, Ord, Repr, Hashable

instance [Ord α]: Ord (Pred α) := inferInstance

instance [Repr α]: Repr (Pred α) := inferInstance

instance [DecidableEq α]: DecidableEq (Pred α) := inferInstance

instance [DecidableEq α]: BEq (Pred α) := inferInstance

instance [Hashable α]: Hashable (Pred α) := inferInstance

def Pred.eval {α: Type} [BEq α] (p: Pred α) (x: α): Prop :=
  match p with
  | Pred.eq y => x = y
  | Pred.any => True

def Pred.pred_is_decpred {α : Type} [d: DecidableEq α] (p: Pred α): (a: α) -> Decidable (Pred.eval p a) :=
  fun x =>
    match p with
    | Pred.eq y => d x y
    | Pred.any => Decidable.isTrue True.intro

def Pred.decidablePredEval {α: Type} [BEq α] [d: DecidableEq α] (p: Pred α) : DecidablePred p.eval :=
  Pred.pred_is_decpred p

instance inst_pred_decrel {α: Type} [d: DecidableEq α]: DecidableRel (Pred.eval (α := α)) :=
  Pred.decidablePredEval

instance inst_pred_decpred {α: Type} [d: DecidableEq α] (p: Pred α): DecidablePred p.eval :=
  p.decidablePredEval

instance inst_pred_dec {α: Type} [d: DecidableEq α] (p: Pred α) (a: α): Decidable (p.eval a) :=
  p.decidablePredEval a

-- Test that LawfulBEq is inferred for our specific inductive type
instance inst_pred_lbeq {α: Type} [DecidableEq (Pred α)]: LawfulBEq (Pred α) := inferInstance

-- Test that BEq is inferred for our specific inductive type
instance inst_pred_beq {α: Type} [DecidableEq (Pred α)]: BEq (Pred α) := inferInstance

def Pred.eq_of_beq {α: Type} {a b : Pred α} [d: DecidableEq (Pred α)]
  (heq: a == b): a = b := of_decide_eq_true heq

def Pred.eq_of_beq' {α: Type} {a b : Pred α} [d: DecidableEq (Pred α)] (heq: a == b): a = b := by
  refine @of_decide_eq_true (a = b) (d a b) heq

def Pred.rfl {α: Type} {a : Pred α} [d: DecidableEq (Pred α)]: a == a := of_decide_eq_self_eq_true a

instance inst_deq_lbeq {α: Type} [DecidableEq (Pred α)]: LawfulBEq (Pred α) where
  eq_of_beq : {a b : Pred α} → a == b → a = b := Pred.eq_of_beq
  rfl : {a : Pred α} → a == a := Pred.rfl

def Pred.evalb {α: Type} [DecidableEq α] (p: Pred α) (x: α): Bool :=
  Pred.eval p x
