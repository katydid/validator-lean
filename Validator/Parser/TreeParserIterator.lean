import Init.Data.Iterators

import Validator.Parser.Hint
import Validator.Std.ParseTree
import Validator.Parser.TreeParser

namespace TreeParserIterator

structure TreeParserIterator (α : Type) where
  state : TreeParser.ParserState α

def ParseForest.iterM {α : Type} (forest : ParseForest α) (m : Type → Type w') [Pure m] :
  Std.Iterators.IterM (α := TreeParserIterator α) m α :=
    Std.Iterators.toIterM { state := TreeParser.ParserState.mks forest } m α

def PlausibleIterStep (IsPlausibleStep : Std.Iterators.IterStep α β → Prop) := Subtype IsPlausibleStep
class Iterator (α : Type w) (m : Type w → Type w') (β : outParam (Type w)) where
  IsPlausibleStep : Std.Iterators.IterM (α := α) m β → Std.Iterators.IterStep (Std.Iterators.IterM (α := α) m β) β → Prop
  step : (it : Std.Iterators.IterM (α := α) m β) → m (PlausibleIterStep (IsPlausibleStep it))

instance {α : Type} [Pure m] : Std.Iterators.Iterator (TreeParserIterator α) m Hint where
  IsPlausibleStep
    (currentState: @Std.IterM (TreeParserIterator α) m Hint)
    (iterStep: Std.Iterators.IterStep (@Std.Iterators.IterM (TreeParserIterator α) m Hint) Hint): Prop :=
    match iterStep with
    | .skip _ => False
    | .done => currentState.internalState.state.current = TreeParser.CurrentState.eof
    | .yield nextState nextHint =>
      nextHint ≠ Hint.eof /\
      Except.ok (nextHint, nextState.internalState.state) = TreeParser.run (TreeParser.next (α := α)) currentState.internalState.state
  step (it: @Std.IterM (TreeParserIterator α) m Hint)
    -- def PlausibleIterStep
    --   (IsPlausibleStep : Std.Iterators.IterStep (@Std.Iterators.IterM (TreeParserIterator α) m Hint) Hint → Prop) :=
    --   Subtype IsPlausibleStep
    -- : m (PlausibleIterStep (IsPlausibleStep it))
    := by
      let ⟨ ⟨ current, stack ⟩ ⟩ := it
      cases current with
      | unknown children =>
        refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
        · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.opened children) stack)
        · exact Hint.enter
        · simp
          rw [<- TreeParser.next_unknown_gt_opened]
      | field f children =>
        refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
        · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.opened children) stack)
        · exact Hint.enter
        · simp
          rw [<- TreeParser.next_field_gt_opened]
      | pair f v children =>
        refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
        · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.value v children) stack)
        · exact Hint.value
        · simp
          rw [<- TreeParser.next_pair_gt_value]
      | opened children =>
        cases children with
        | nil =>
          cases stack with
          | nil =>
            refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
            · exact (TreeParser.ParserState.mk TreeParser.CurrentState.eof [])
            · exact Hint.leave
            · simp
              rw [TreeParser.next_opened_gt_popped_opened_eof]
          | cons s ss =>
            refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
            · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.opened s) ss)
            · exact Hint.leave
            · simp
              rw [TreeParser.next_opened_gt_popped_opened_more]
        | cons child siblings =>
          cases child with
          | mk f fchildren =>
            cases fchildren with
            | nil =>
              refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
              · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.value f siblings) stack)
              · exact Hint.value
              · simp
                rw [TreeParser.next_opened_value_gt_value]
            | cons fchild1 fchildren =>
              cases fchildren with
              | nil =>
                cases fchild1 with
                | mk v vchildren =>
                cases vchildren with
                | nil =>
                  refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
                  · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.pair f v siblings) stack)
                  · exact Hint.field
                  · simp
                    rw [TreeParser.next_opened_pair_gt_pair]
                | cons vchild vchildren =>
                  refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
                  · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.field f [ParseTree.mk v (vchild::vchildren)]) (siblings::stack))
                  · exact Hint.field
                  · simp
                    rw [TreeParser.next_opened_gt_push]
                    left
                    exists v
                    exists vchild
                    exists vchildren
              | cons fchild2 fchildren =>
                refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
                · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.field f (fchild1::fchild2::fchildren)) (siblings::stack))
                · exact Hint.field
                · simp
                  rw [TreeParser.next_opened_gt_push]
                  right
                  exists fchild1
                  exists fchild2
                  exists fchildren
      | value v children =>
        cases children with
        | nil =>
          cases stack with
          | nil =>
            refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
            · exact (TreeParser.ParserState.mk TreeParser.CurrentState.eof [])
            · exact Hint.leave
            · simp
              rw [TreeParser.next_value_gt_popped_value_eof]
          | cons s ss =>
            refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
            · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.opened s) ss)
            · exact Hint.leave
            · simp
              rw [TreeParser.next_value_gt_popped_value_more]
        | cons child siblings =>
          cases child with
          | mk f fchildren =>
            cases fchildren with
            | nil =>
              refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
              · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.value f siblings) stack)
              · exact Hint.value
              · simp
                rw [TreeParser.next_value_value_gt_value]
            | cons fchild1 fchildren =>
              cases fchildren with
              | nil =>
                cases fchild1 with
                | mk v vchildren =>
                cases vchildren with
                | nil =>
                  refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
                  · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.pair f v siblings) stack)
                  · exact Hint.field
                  · simp
                    rw [TreeParser.next_value_pair_gt_pair]
                | cons vchild vchildren =>
                  refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
                  · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.field f [ParseTree.mk v (vchild::vchildren)]) (siblings::stack))
                  · exact Hint.field
                  · simp
                    rw [TreeParser.next_value_gt_push]
                    left
                    exists v
                    exists vchild
                    exists vchildren
              | cons fchild2 fchildren =>
                refine (pure ⟨ Std.Iterators.IterStep.yield ⟨TreeParserIterator.mk ?_⟩ ?_, ?_ ⟩ )
                · exact (TreeParser.ParserState.mk (TreeParser.CurrentState.field f (fchild1::fchild2::fchildren)) (siblings::stack))
                · exact Hint.field
                · simp
                  rw [TreeParser.next_value_gt_push]
                  right
                  exists fchild1
                  exists fchild2
                  exists fchildren
      | eof =>
        refine (pure ⟨ Std.Iterators.IterStep.done, ?_ ⟩ )
        simp

private def TreeParserIterator.finitenessRelation [Pure m] :
    Std.Iterators.FinitenessRelation (TreeParserIterator α) m where
  rel := InvImage WellFoundedRelation.rel (TreeParserIterator.state ∘ Std.Iterators.IterM.internalState)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    clean_wf
    simp only [Function.comp]
    obtain ⟨step, h, h'⟩ := h
    cases step with
    | skip =>
      simp_all [Std.Iterators.IterStep.successor, Std.Iterators.IterM.IsPlausibleStep, Std.Iterators.Iterator.IsPlausibleStep]
    | done =>
      simp_all [Std.Iterators.IterStep.successor]
    | yield =>
      rename_i hint
      simp only [Std.Iterators.IterM.IsPlausibleStep, Std.Iterators.Iterator.IsPlausibleStep] at h'
      simp [Std.Iterators.IterStep.successor] at h
      rw [h] at h'
      obtain ⟨ hneof, h' ⟩ := h'
      exact TreeParser.next_decreases_size_of_parserstate hneof h'

instance [Pure m] : Std.Iterators.Finite (TreeParserIterator α) m :=
  Std.Iterators.Finite.of_finitenessRelation TreeParserIterator.finitenessRelation

@[always_inline, inline]
instance {α : Type} [Monad m] {n : Type → Type w''} [Monad n] :
    Std.Iterators.IteratorCollect (TreeParserIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type} [Monad m] {n : Type → Type w''} [Monad n] :
    Std.Iterators.IteratorCollectPartial (TreeParserIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type} [Monad m] {n : Type → Type x'} [Monad n] :
    Std.Iterators.IteratorLoop (TreeParserIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type} [Monad m] {n : Type → Type x'} [Monad n] :
    Std.Iterators.IteratorLoopPartial (TreeParserIterator α) m n :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type} [Monad m] : Std.Iterators.IteratorSize (TreeParserIterator α) m :=
  .defaultImplementation

@[always_inline, inline]
instance {α : Type} [Monad m] : Std.Iterators.IteratorSizePartial (TreeParserIterator α) m :=
  .defaultImplementation
