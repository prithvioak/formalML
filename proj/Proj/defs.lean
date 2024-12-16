import Mathlib
-- open MeasureTheory ProbabilityTheory
-- open Random
-- open scoped ENNReal


namespace defs

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

def twoattr_linear_classifier (w1 w2 b : ℚ) : ℚ × ℚ → Bool :=
  λ x => x.1 * w1 + x.2 * w2 + b > 0

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

def accuracy (predictions : List Bool) (labels : List Bool) (_ : predictions.length = labels.length ∧ predictions.length > 0) : ℚ :=
  (meld (λ p l => if p = l then 1 else 0) predictions labels).sum / predictions.length

#eval accuracy ([true, false, true]) ([true, true, true]) (by simp)



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

-- Proofs about classifiers now!

-- Hypothesis classes:
-- Defining the hypothesis class for the threshold classifier
def thresholdHypothesisClass : Set (ℚ → Bool) :=
  {threshold_classifier t | t : ℚ}
def halfspaceHypothesisClass : Set ((ℚ × ℚ) → Bool) :=
  {h | ∃ w1 w2 b : ℚ, h = twoattr_linear_classifier w1 w2 b}

-- Defining the equivalence function for the halfspace classifier
def h_equiv (x1 x2 : ℚ) : Bool :=
  if x1 = x2 then true else false

-- Next: Implementing the Perceptron algorithm (and proving its convergence?)


end defs
