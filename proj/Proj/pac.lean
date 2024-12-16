import Mathlib
-- open MeasureTheory ProbabilityTheory
-- open Random
-- open scoped ENNReal


namespace formalML

set_option linter.deprecated false

-- Let's start with defining some basic kinds of hypotheses and loss functions!

-- We define this over the real numbers for evaluability
def threshold_classifier (t : ℚ) : ℚ → Bool :=
  λ x => x > t

def interval_classifier (l : ℚ) (u : ℚ) : ℚ → Bool :=
  λ x => x > l ∧ x < u

#eval (threshold_classifier 5) 6

def linear_classifier (w : ℚ) (b : ℚ) : ℚ → Bool :=
  λ x => x * w + b > 0

#eval (linear_classifier 2 (-1)) 0

-- Meld from homework1!
def meld {α β γ : Type} : (α → β → γ) → List α → List β → List γ
  := fun
  | _, [], _ => []
  | _, _, [] => []
  | f, a :: as, b :: bs => f a b :: meld f as bs

-- def multiclassClassifier (w : List ℚ) (b : ℚ) (x : List ℚ) (_ : w.length = x.length) : Bool :=
--   (meld (λ w_i x_i => w_i * x_i) w x).sum + b > 0
def multiattr_linear_classifier (w : List ℚ) (b : ℚ) : List ℚ → Bool :=
  λ x => (meld (λ w_i x_i => w_i * x_i) w x).sum + b > 0

-- variable {w x : List ℚ}
-- #check (meld (λ w_i x_i => w_i * x_i) w x)

def c : List ℚ := [1,2,10]
def d : List ℚ := [1,14,-3]
#eval multiattr_linear_classifier c 1 d

#check List.foldl

def zeroOneLoss (y_true : Bool) (y_pred : Bool) : ℚ :=
  if y_true = y_pred then 0 else 1

#eval zeroOneLoss true true
#eval zeroOneLoss true false

def squared_loss (prediction : ℚ) (label : ℚ) : ℚ :=
  (prediction - label) ^ 2

#eval squared_loss 5 3

-- A dataset is a list of (input, label) pairs
def dataset (inputType: Type) (labelType : Type) := List (inputType × labelType)

def evaluate_hypothesis {α β : Type} (h : α → β) (data : dataset α β) : List β :=
  data.map (λ pair => h pair.1)

def exampleData1 : dataset ℚ Bool := [(4, true), (6, false)]
#eval evaluate_hypothesis (threshold_classifier 5) exampleData1
def exampleData2 : dataset (List ℚ) Bool := [([1,2,10], true), ([1,14,-3], false)]
#eval evaluate_hypothesis (multiattr_linear_classifier [1,2,10] 1) exampleData2

def calculate_loss_real (loss : ℚ → ℚ → ℚ) (h : ℚ → Bool) (data : dataset ℚ Bool) : ℚ :=
  (data.map (λ pair => loss (if h pair.1 then 1 else 0) (if pair.2 then 1 else 0))).sum

def calculate_loss_bool (loss : Bool → Bool → ℚ) (h : ℚ → Bool) (data : dataset ℚ Bool) : ℚ :=
  (data.map (λ pair => loss (h pair.1) pair.2)).sum

def calculate_loss_multivar (loss : Bool → Bool → ℚ) (h : List ℚ → Bool) (data : dataset (List ℚ) Bool) : ℚ :=
  (data.map (λ pair => loss (h pair.1) pair.2)).sum

#eval calculate_loss_real squared_loss (threshold_classifier 5) exampleData1
#eval calculate_loss_bool zeroOneLoss (linear_classifier 2 1) exampleData1

def accuracy (predictions : List Bool) (labels : List Bool) (hpl : predictions.length = labels.length ∧ predictions.length > 0) : ℚ :=
  (meld (λ p l => if p = l then 1 else 0) predictions labels).sum / predictions.length

#eval accuracy ([true, false, true]) ([true, true, true]) (by simp)


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


-- Proving convexity of squared loss

lemma sq_of_dec (α : ℚ) (h : 0 ≤ α ∧ α ≤ 1) : α^2 ≤ α :=
  by
  apply sq_le h.left h.right

theorem squared_loss_convex:
  ∀ (α p1 p2 label: ℚ), 0 ≤ α ∧ α ≤ 1 → squared_loss (α * p1 + (1 - α) * p2) label ≤ α * squared_loss p1 label + (1 - α) * squared_loss p2 label :=
  by
    intro α p1 p2 label hα
    rw [squared_loss, squared_loss, squared_loss]
    let lhs := (α * p1 + (1 - α) * p2 - label) ^ 2
    let rhs := α * (p1 - label) ^ 2 + (1 - α) * (p2 - label) ^ 2
    have lhs_expand : lhs = α^2 * (p1 - label)^2 + (1 - α)^2 * (p2 - label)^2 + 2 * α * (1 - α) * (p1 - label) * (p2 - label) := by ring
    -- Expand the left-hand side (LHS)
    have key_inequality : 2 * α * (1 - α) * (p1 - label) * (p2 - label) ≤ 0 := by
    -- 2 * α * (1 - α) is non-negative because 0 ≤ α ≤ 1
      apply mul_nonpos_of_nonneg_of_nonpos
      { apply mul_nonneg
        {
          let hhelp : 0 ≤ (1 - α) := by simp [hα.right]
          let haa' : 0 ≤ α * (1 - α) := mul_nonneg hα.left hhelp
          linarith
        }
        {
          sorry
        }
      }
      { sorry }

    calc
      _ = α^2 * (p1 - label)^2 + (1 - α)^2 * (p2 - label)^2 + 2 * α * (1 - α) * (p1 - label) * (p2 - label) := by apply lhs_expand
      _ ≤ α^2 * (p1 - label)^2 + (1 - α)^2 * (p2 - label)^2 := by linarith
      _ ≤ rhs :=
        by
        let haasq : α ^ 2 ≤ α := by apply sq_of_dec α hα
        let hα' : 0 ≤ 1 - α ∧ 1 - α ≤ 1 := And.intro (by linarith) (by linarith)
        let h1asq : (1 - α) ^ 2 ≤ 1 - α := by apply sq_of_dec (1 - α) hα'
        let hppos : 0 ≤ (p1 - label) ^ 2 := by exact sq_nonneg (p1 - label)
        let hppos' : 0 ≤ (p2 - label) ^ 2 := by exact sq_nonneg (p2 - label)
        let h1 : α^2 * (p1 - label)^2 ≤ α * (p1 - label)^2 := by
          exact mul_le_mul_of_nonneg_right haasq hppos
        let h2 : (1 - α)^2 * (p2 - label)^2 ≤ (1 - α) * (p2 - label)^2 := by
          exact mul_le_mul_of_nonneg_right h1asq hppos'
        exact add_le_add h1 h2

  -- Expand and simplify
  -- apply le_of_sub_nonneg


-- Proofs about classifiers now!

/- Proving that the halfspace classifier (linear classifier)
   cannot classify all points of a described labelling -/
-- TO NOTE: Defining the labelling as a function allows much more ease in proofs without sacrificing generality

def twoattr_linear_classifier (w1 w2 b : ℚ) : ℚ × ℚ → Bool :=
  λ x => x.1 * w1 + x.2 * w2 + b > 0

def h_equiv (x1 x2 : ℚ) : Bool :=
  if x1 = x2 then true else false

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


-- Adding new definitions

-- Shattering of a set:
/- A hypothesis class H shatters a finite set S ⊆ X if, for every possible assignment of
outputs to the points in S, there’s some h ∈ H that induces it. -/

def shatters {X : Type} (H : Set (X → Bool)) (S : Finset X) : Prop :=
    ∀ (label : X → Bool), ∃ h ∈ H, ∀ x ∈ S, h x = label x


-- Length of a finite set is cardinality in mathlib
-- #eval Finset.card {1, 2, 3}

-- What does it mean for VC dimension to be n?
def VCdim {X : Type} (H : Set (X → Bool)) (n : ℕ) : Prop :=
  (∃ (S : Finset X), S.card = n ∧ shatters H S) ∧
    (∀ (S' : Finset X), S'.card = n + 1 → ¬ shatters H S')
-- VC dimension of a hypothesis class is the size of the largest set that can be shattered by it

lemma non_zero_card (S : Finset ℚ) : S.card ≠ 0 → S.Nonempty :=
  by
  intro h
  exact Finset.card_ne_zero.mp h

-- TRY TO PROVE THIS IF POSSIBLE
axiom elems_of_finset_greater (S : Finset ℚ) (hS : S.card = 2) (hS2 : S.Nonempty): S.max' hS2 > S.min' hS2

def FS : Finset ℚ := {1, 2, 3}
def FS_nonzerocard : FS.card ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one (List.insert 2 [3]).length)
-- #eval FS.max' (non_zero_card FS FS_nonzerocard)
#eval FS.min
-- #check Finset.Nonempty

-- Defining the hypothesis class for the threshold classifier
def thresholdHypothesisClass : Set (ℚ → Bool) :=
  {threshold_classifier t | t : ℚ}

def threshold_breaker (max_elem : ℚ) : ℚ → Bool :=
  λ x => x < max_elem

-- Proving that the VC dimension of the threshold classifier is 1
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

-- Let's specify this for the halfspace classifier!

def halfspaceHypothesisClass : Set ((ℚ × ℚ) → Bool) :=
  {h | ∃ w1 w2 b : ℚ, h = twoattr_linear_classifier w1 w2 b}

-- Proving that the VC dimension of the halfspace classifier is 3
theorem halfspace_VCdim_3 :
  -- Taking a basic linear classifier for the proof, this can be generalized
  VCdim halfspaceHypothesisClass 3 :=
  by
  apply And.intro
  {
    apply Exists.intro {1, 2, 3}
    apply And.intro
    {
      exact rfl
    }
    {
      intro label
      let hhelp : label (1, 1) = true ∨ label (1, 1) = false := by simp
      sorry
      -- apply And.intro
      -- {
      --   simp
      -- }
      -- {
      --   simp [twoattr_linear_classifier]
      --   match x with
      --   | 1 =>
      --     simp

      --   | 2 => simp
      --   | 3 => simp
      -- }
    }
  }
  {
    intro S' hS'
    simp at hS'
    sorry
    -- cases hS' with
    --   cases S' with
    --   | nil => simp [shatters]
    --   | cons x xs =>
    --     cases xs with
    --     | nil => simp [shatters]
    --     | cons x' xs' =>
    --       cases xs' with
    --       | nil => simp [shatters]
    --       | cons x'' xs'' =>
    --         simp [shatters]
    --         intro h
    --         cases h with
    --         | intro h hfin =>
    --           let h1 := hfin 1 (by simp)
    --           let h2 := hfin 2 (by simp)
    --           let h3 := hfin 3 (by simp)
    --           simp [twoattr_linear_classifier] at h1 h2 h3
    --           linarith
  }

-- Next: Implementing the Perceptron algorithm (and proving its convergence?)


end formalML
