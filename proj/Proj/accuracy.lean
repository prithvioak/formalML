import Proj.defs
open defs

namespace acc

-- Time for some proofs!

-- Proving that accuracy is always between 0 and 1
-- lemma sum_nonneg_nonneg

lemma bound_indiv0 : ∀ (p l : Bool), (0 : ℚ) ≤ (λ p' l' => if p' = l' then 1 else 0) p l :=
  by
  intro p l
  cases p with
  | true =>
    cases l with
    | true => simp [Nat.zero_le]
    | false => simp [Nat.zero_le]
  | false =>
    cases l with
    | true => simp [Nat.zero_le]
    | false => simp [Nat.zero_le]

lemma bound_indiv1: ∀ (p l : Bool), (1 : ℚ) ≥ (λ p' l' => if p' = l' then 1 else 0) p l :=
  by
  intro p l
  cases p with
  | true =>
    cases l with
    | true => exact rfl
    | false => exact rfl
  | false =>
    cases l with
    | true => exact rfl
    | false => exact rfl

lemma meldpos (f : Bool → Bool → ℚ) (p : List Bool) (l : List Bool) :
  (∀ (x y : Bool), 0 ≤ f x y) → (meld f p l).sum ≥ 0 :=
  by
  intro h
  induction p generalizing l with
  | nil => simp [meld]
  | cons p ps ih =>
    cases l with
    | nil => simp [meld]
    | cons l ls =>
      simp [meld]
      apply add_nonneg
      {exact h p l}
      {exact ih ls}

lemma meldpos' (f : Bool → Bool → ℚ) (p : List Bool) (l : List Bool) :
  (∀ (x y : Bool), 1 ≥ f x y) → (meld f p l).sum ≤ p.length :=
  by
  intro h
  induction p generalizing l with
  | nil => simp [meld]
  | cons p ps ih =>
    cases l with
    | nil =>
      simp [meld]
      let hps : ps.length >= (0 : ℚ) := by exact Nat.cast_nonneg' ps.length
      calc
        (0 : ℚ) ≤ ps.length := hps
        _ ≤ ps.length + 1 := by simp
    | cons l ls =>
      simp [meld]
      -- apply add_le_add
      have h' : (meld f ps ls).sum ≤ ps.length := by exact ih ls
      have h'' : f p l ≤ 1 := by exact h p l
      calc
        f p l + (meld f ps ls).sum  ≤ 1 + ps.length := by exact add_le_add (h p l) (ih ls)
        _ = ps.length + 1 := by exact Rat.add_comm 1 ↑ps.length

opaque predictions : List Bool
opaque labels : List Bool
#check meldpos (λ p l => if p = l then 1 else 0) predictions labels bound_indiv0

lemma div_both_sides (a b c : ℚ) (h : b > 0) : a ≤ c ↔ a / b ≤ c / b :=
  by
  apply Iff.intro
  {
    intro h'
    exact (div_le_div_right h).mpr h'
  }
  {
    intro h'
    let hneq0 : b ≠ 0 := by linarith
    have h'' : a = a / b * b := by exact Eq.symm (div_mul_cancel₀ a hneq0)
    have h''' : c = c / b * b := by exact Eq.symm (div_mul_cancel₀ c hneq0)
    rw [h'', h''']
    exact (mul_le_mul_iff_of_pos_right h).mpr h'
  }

lemma self_div (a : ℚ) (ha : a ≠ 0): a / a = 1 :=
  by
  exact (div_eq_one_iff_eq ha).mpr rfl

lemma listlens (ps : List Bool) : ps.length > 0 → ps ≠ [] :=
  by
  intro h
  let h' : ps.length ≠ 0 := by exact Nat.not_eq_zero_of_lt h
  cases ps with
  | nil => exact False.elim (h' rfl)
  | cons p ps' => exact List.cons_ne_nil p ps'

theorem accuracy_bounds (predictions : List Bool) (labels : List Bool) (hpl : predictions.length = labels.length ∧ predictions.length > 0) :
  0 ≤ accuracy predictions labels hpl ∧ accuracy predictions labels hpl ≤ 1 :=
  by
  -- simp [accuracy, List.sum]
  apply And.intro
  {
    apply div_nonneg
    {
      let hm := meldpos (λ p l => if p = l then 1 else 0) predictions labels bound_indiv0
      exact hm
    }
    {exact Nat.cast_nonneg' predictions.length}
  }
  {
    have h' : List.sum (meld (λ p l => if p = l then (1 : ℚ) else 0) predictions labels) ≤ predictions.length := by
      let hm := meldpos' (λ p l => if p = l then 1 else 0) predictions labels bound_indiv1
      exact hm
    let hnew := div_both_sides (List.sum (meld (λ p l => if p = l then (1 : ℚ) else 0) predictions labels))
                               predictions.length
                               predictions.length
                               (
                                by
                                simp [hpl.right]
                               )
    let hnewapplied := hnew.mp h'
    let hdivdiv : predictions.length / predictions.length = 1 := by
      simp [hpl.right]
    rw [accuracy]
    calc
      (meld (fun p l ↦ if p = l then (1 : ℚ) else 0) predictions labels).sum / predictions.length ≤ predictions.length / predictions.length := by
        exact hnewapplied
      _ = 1 := by apply self_div predictions.length
                                 (
                                  by
                                  simp [hpl.right]
                                  apply Ne.symm
                                  apply Ne.symm
                                  apply listlens predictions hpl.right
                                 )
  }
-- Much longer than I expected, but it works!



end acc
