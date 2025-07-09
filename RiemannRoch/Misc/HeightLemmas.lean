import Mathlib

/-!
# Height lemmas

These are some lemmas useful for proving that the codimension of a point is equal
to the dimension of its stalk.
-/

variable {α β : Type*}
variable [Preorder α] [Preorder β]

namespace Order

lemma height_eq_of_strictMono (f : α → β) (hf : StrictMono f) (a : α)
    (h : ∀ p : LTSeries β, p.last = f a → ∃ p' :
    LTSeries α, p'.last = a ∧ p = p'.map f hf) : height a = height (f a) := by
  apply eq_of_le_of_le <|
    Order.height_le_height_apply_of_strictMono _ hf _
  refine height_le_iff'.mpr (fun p hp ↦ ?_)
  choose p' hp' using (h p hp)
  exact hp'.2 ▸ LTSeries.map_length p' f hf ▸
        (Order.height_eq_iSup_last_eq a) ▸
        (ciSup_pos hp'.1 : (⨆ (_ : RelSeries.last p' = a), p'.length : ℕ∞) = p'.length) ▸
        le_iSup (α := ℕ∞) (fun p ↦ ⨆ (_ : RelSeries.last p = a), p.length) p'

lemma coheight_eq_of_strictMono  (f : α → β) (hf : StrictMono f) (a : α)
    (h : ∀ p : LTSeries β, p.head = f a → ∃ p' :
    LTSeries α, p'.head = a ∧ p = p'.map f hf) : coheight a = coheight (f a) := by
  apply eq_of_le_of_le <|
    Order.coheight_le_coheight_apply_of_strictMono _ hf _
  refine coheight_le_iff'.mpr (fun p hp ↦ ?_)
  choose p' hp' using (h p hp)
  exact hp'.2 ▸ LTSeries.map_length p' f hf ▸
        (Order.coheight_eq_iSup_head_eq a) ▸
        (ciSup_pos hp'.1 : (⨆ (_ : RelSeries.head p' = a), p'.length : ℕ∞) = p'.length) ▸
        le_iSup (α := ℕ∞) (fun p ↦ ⨆ (_ : RelSeries.head p = a), p.length) p'
