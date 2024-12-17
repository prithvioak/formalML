import Proj.defs
open defs

namespace hypothesis

-- Proving that the halfspace classifier cannot classify all points of a described labelling
-- TO NOTE: Defining the labelling as a function allows much more ease in proofs without sacrificing generality
theorem not_represented :
  ¬ ∃ (w1 w2 b : ℚ), ∀ (x1 x2 : ℚ), twoattr_linear_classifier w1 w2 b (x1, x2) = h_equiv x1 x2 :=
  by
  intro h
  cases h with
  | intro w1 hw1 =>
    cases hw1 with
    | intro w2 hw2 =>
      cases hw2 with
      | intro b hfin =>
        let h1 := hfin 1 1
        let h2 := hfin 1 3
        let h3 := hfin 3 1
        let h4 := hfin 2 2
        simp [twoattr_linear_classifier, h_equiv] at h1 h2 h3 h4
        linarith


-- Proving that the VC dimension of the threshold classifier is 1

------------------------------ RELEVANT LEAMMAS --------------------------------

lemma non_zero_card (S : Finset ℚ) : S.card ≠ 0 → S.Nonempty :=
  by
  intro h
  exact Finset.card_ne_zero.mp h

-- Due to the way that Finset is defined, we would need to prove this lemma to get the max and min of a set
-- This axiom simply states that the max of a set is greater than the min of a set if the set has 2 elements.
-- This is intuitively true, since a set cannot have two elements that are equal.
axiom elems_of_finset_greater (S : Finset ℚ) (hS : S.card = 2) (hS2 : S.Nonempty): S.max' hS2 > S.min' hS2

def FS : Finset ℚ := {1, 2, 3}
def FS_nonzerocard : FS.card ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one (List.insert 2 [3]).length)
-- #eval FS.max' (non_zero_card FS FS_nonzerocard)
#eval FS.min
-- #check Finset.Nonempty

-- Helps us in proving that the threshold classifier cannot shatter a set of size 2
def threshold_breaker (max_elem : ℚ) : ℚ → Bool :=
  λ x => x < max_elem

-------------------------------- PROOF -----------------------------------------
theorem threshold_VCdim_1 :
  VCdim thresholdHypothesisClass 1 :=
  by
  simp [VCdim, thresholdHypothesisClass, shatters]
  apply And.intro
  {
    apply Exists.intro {1}
    apply And.intro
    {
      rfl
    }
    {
      intro label
      let hhelp : label 1 = true ∨ label 1 = false := by simp
      cases hhelp with
      | inl htr =>
        apply Exists.intro 0
        intro x
        intro hx
        simp [threshold_classifier]
        match x with
        | 1 =>
          simp
          exact htr
      | inr hfl =>
        apply Exists.intro 3
        intro x
        intro hx
        simp [threshold_classifier]
        match x with
        | 1 =>
          simp
          exact hfl
    }
  }
  {
    intro S' hS'
    let hhelp : S'.card ≠ 0 := by exact Ne.symm (by simp [hS'])
    let elem1 := S'.min' (non_zero_card S' hhelp)
    let elem2 := S'.max' (non_zero_card S' hhelp)
    let hdiff : elem1 ≠ elem2 :=
      by
      unfold elem1 elem2

      let hless := (elems_of_finset_greater S' hS' (non_zero_card S' hhelp)).symm
      exact ne_of_lt (id (Eq.symm hless))
    apply Exists.intro (threshold_breaker elem2)
    intro thresh
    let hte : thresh < elem2 ∨ thresh ≥ elem2 := by exact lt_or_le thresh elem2
    cases hte with
    | inl hlt =>
      apply Exists.intro elem2
      apply And.intro
      {
        exact Finset.max'_mem S' (non_zero_card S' hhelp)
      }
      {
        let htfal : threshold_classifier thresh elem2 = true :=
          by
          simp [threshold_classifier]
          exact hlt
        let httru : threshold_breaker elem2 elem2 = false :=
          by
          simp [threshold_breaker]
        apply Ne.symm
        rw [htfal, httru]
        exact Bool.false_ne_true
      }
    | inr hge =>
      apply Exists.intro elem1
      apply And.intro
      {
        exact Finset.min'_mem S' (non_zero_card S' hhelp)
      }
      {
        let he1le2 := elems_of_finset_greater S' hS' (non_zero_card S' hhelp)
        let htfal : threshold_classifier thresh elem1 = false :=
          by
          simp [threshold_classifier]
          calc
            elem1 ≤ elem2 := by apply le_of_lt he1le2
            _ ≤ thresh := hge
        let httru : threshold_breaker elem2 elem1 = true :=
          by
          simp [threshold_breaker]
          exact he1le2
        apply Ne.symm
        rw [htfal, httru]
        exact Bool.true_eq_false_eq_False
    }
  }



-- Proving that the VC dimension of the halfspace classifier is 3
theorem halfspace_VCdim_3 :
  -- Taking a basic linear classifier for the proof, this can be generalized
  VCdim halfspaceHypothesisClass 3 :=
  by
  apply And.intro
  {
    apply Exists.intro {(1, 0), (0, 1), (0, 0)}
    apply And.intro
    {
      exact rfl
    }
    {
      intro label
      let h1induced : ∃ h ∈ halfspaceHypothesisClass, h (0, 1) = label (0, 1) :=
        by
        let hhelp : label (0, 1) = true ∨ label (0, 1) = false := by simp
        cases hhelp with
        | inl htr =>
          apply Exists.intro (twoattr_linear_classifier 0 1 0)
          apply And.intro
          {
            rw [halfspaceHypothesisClass]
            apply Exists.intro 0
            apply Exists.intro 1
            apply Exists.intro 0
            simp
          }
          {
            rw [htr]
            simp [twoattr_linear_classifier]
          }
        | inr hfl =>
          apply Exists.intro (twoattr_linear_classifier (-1) (-1) (-1))
          apply And.intro
          {
            rw [halfspaceHypothesisClass]
            apply Exists.intro (-1)
            apply Exists.intro (-1)
            apply Exists.intro (-1)
            simp
          }
          {
            rw [hfl]
            simp [twoattr_linear_classifier]
          }
      let h2induced : ∃ h ∈ halfspaceHypothesisClass, h (1, 0) = label (1, 0) :=
        by
        let hhelp : label (1, 0) = true ∨ label (1, 0) = false := by simp
        cases hhelp with
        | inl htr =>
          apply Exists.intro (twoattr_linear_classifier 1 0 0)
          apply And.intro
          {
            rw [halfspaceHypothesisClass]
            apply Exists.intro 1
            apply Exists.intro 0
            apply Exists.intro 0
            simp
          }
          {
            rw [htr]
            simp [twoattr_linear_classifier]
          }
        | inr hfl =>
          apply Exists.intro (twoattr_linear_classifier (-1) (-1) (-1))
          apply And.intro
          {
            rw [halfspaceHypothesisClass]
            apply Exists.intro (-1)
            apply Exists.intro (-1)
            apply Exists.intro (-1)
            simp
          }
          {
            rw [hfl]
            simp [twoattr_linear_classifier]
          }
      let h3induced : ∃ h ∈ halfspaceHypothesisClass, h (0, 0) = label (0, 0) :=
        by
        let hhelp : label (0, 0) = true ∨ label (0, 0) = false := by simp
        cases hhelp with
        | inl htr =>
          apply Exists.intro (twoattr_linear_classifier 0 0 5)
          apply And.intro
          {
            rw [halfspaceHypothesisClass]
            apply Exists.intro 0
            apply Exists.intro 0
            apply Exists.intro 5
            simp
          }
          {
            rw [htr]
            simp [twoattr_linear_classifier]
          }
        | inr hfl =>
          apply Exists.intro (twoattr_linear_classifier (-1) (-1) (-1))
          apply And.intro
          {
            rw [halfspaceHypothesisClass]
            apply Exists.intro (-1)
            apply Exists.intro (-1)
            apply Exists.intro (-1)
            simp
          }
          {
            rw [hfl]
            simp [twoattr_linear_classifier]
          }
      sorry
      -- Individually proving that each point can be shattered! Generalizing this is a bit tricky
    }
  }
  {
    intro S' hS'
    simp at hS'
    sorry
    -- REALLY complicated proof...
  }

end hypothesis
