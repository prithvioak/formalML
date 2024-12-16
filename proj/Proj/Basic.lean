namespace fallacyFormalization

-- #eval 5 + 5 + 5

set_option linter.deprecated false

structure Argument :=
  (premises : List Prop)
  (conclusion : Prop)
  -- (arg_type : String)

-- Introducing the notion of necessity to formalize the concept of entailment
-- AND handling the case of things that are not necessarily true
opaque necessarily : Prop → Prop

def premises_true (arg : Argument) : Prop :=
  ∀ p ∈ arg.premises, p

-- def premises_true (arg : Argument) : Prop :=
--   List.foldl And True arg.premises
-- Decide which definition to use

def Argument.valid (arg : Argument) : Prop :=
  necessarily (premises_true arg → arg.conclusion)

def Argument.sound (arg : Argument) : Prop :=
  Argument.valid arg ∧ necessarily (premises_true arg)

def Argument.unsound (arg : Argument) : Prop :=
  ¬ Argument.sound arg

def Argument.fallacious (arg : Argument) : Prop :=
  ¬ Argument.valid arg
  -- An argument is fallacious if the premises do not necessarily entail the conclusion

-- Defiining sylllogism?


def Argument.acceptable (arg : Argument) : Prop :=
  Argument.valid arg ∧ Argument.sound arg

theorem Argument.acceptable_iff_sound (arg : Argument) : Argument.acceptable arg ↔ Argument.sound arg := by
  apply Iff.intro
  {
    intro h
    exact h.right
  }
  {
    intro h
    let h1 := h.left
    exact And.intro h1 h
  }

-- Now the real stuff: Fallacies!

-- strawman argument: misrepresenting someone's argument to make it easier to attack
-- In other words, a strawman argument is an argument that is based on misrepresentation of an opponent's position;
-- the premise of the argument is not the actual position of the opponent.
-- Example: "We should relax the laws on beer" "No, any society with unrestricted access to intoxicants loses its work ethic and goes up in smoke."
def strawman_fallacy (original : Argument) (misrepresentation : Argument) :=
  necessarily (Argument.valid original) → ∃ p, p ∈ misrepresentation.premises ∧
                                 p ∉ original.premises ∧
                                 p ≠ original.conclusion

theorem strawman_fallacious (original : Argument) (misrepresented : Argument) :
    strawman_fallacy original misrepresented →
      Argument.valid original →
        Argument.fallacious misrepresented :=
  by
  intro h horig
  rw [Argument.valid] at horig
  have h1 := h horig
  have ⟨p, hp_mis, hp_orig, hp_concl⟩ := h horig
  rw [Argument.fallacious, Argument.valid, premises_true]
  intro h2

  -- let hp : ∀ (p : Prop), p ∈ misrepresented.premises → p :=
  --   by
  --   intro p'


-- red herring



-- circular reasoning
def circular_reasoning (arg : Argument) : Prop :=
  arg.conclusion ∈ arg.premises

theorem circular_reasoning_fallacious (arg : Argument) :
  circular_reasoning arg → Argument.fallacious arg :=
  by
  intro h
  rw [Argument.fallacious, Argument.valid, premises_true]
  intro h1
  rw [circular_reasoning] at h


-- ad hominem??


-- appeal to authority


-- appeal to ignorance

-- appeal to popularity

-- Hasty generalization

-- False dilemma

-- Slippery slope

-- Begging the question -- show that this is equivalent to circular reasoning

-- causal fallacy (Whenever I wear my lucky jersey, my team loses. So it must actually be my unlucky jersey!)

-- fallacy of composition (Every part of the boat is light, so the boat is light.)

-- fallacy of division (The boat is light, so every part of the boat is light.)

-- possible alternative: inductive types for fallacies?

-- inductive Fallacy
--   | Strawman : Argument → Argument → Fallacy
--   | RedHerring : Argument → Fallacy
--   | CircularReasoning : Argument → Fallacy
--   | AdHominem : Argument → Fallacy
--   | AppealToAuthority : Argument → Fallacy
--   | AppealToIgnorance : Argument → Fallacy
--   | AppealToPopularity : Argument → Fallacy
--   | HastyGeneralization : Argument → Fallacy
--   | FalseDilemma : Argument → Fallacy
--   | SlipperySlope : Argument → Fallacy
--   | BeggingTheQuestion : Argument → Fallacy





-- -- A hypothesis is a function from the instance space to the label space
-- def Hypothesis (X : Type) (Y : Type) := X → Y
-- -- Example hypothesis: a linear classifier for real numbers
-- def linearHypothesis : Hypothesis ℝ ℝ := λ x => 2 * x + 1
-- -- In this case, X can be a single instance or a list of instances (representing a sample)

-- -- A hypothesis class is a finite set of hypotheses (for the purpose of PAC learning and VC dimension)
-- def HypothesisClass (X : Type) (Y : Type) := Finset (Hypothesis X Y)

-- -- A loss function is a function from the instance space and the label space to the real numbers
-- def Loss (X : Type) (Y : Type) := X → Y → ℝ
-- -- Example loss function: squared loss
-- def squaredLoss : Loss ℝ ℝ := λ x y => (x - y) ^ 2

-- A PAC learning setup consists of the following components:


structure PACLearning :=
(X : Type)            -- Instance space
(H : Type)            -- Hypothesis space
(Hfin : Finset H)      -- Finite hypothesis space
(D : X → ℝ)           -- True distribution
(loss : X → H → ℝ)    -- Loss function
(realizable : ∃ h ∈ Hfin, ∀ x : X, loss x h = 0)

-- Simple example of a PAC learning setup
noncomputable
example : PACLearning := {
  X := ℝ,
  H := ℝ,
  Hfin := {0, 1},
  D := λ x => 0,
  loss := λ x h => 0,
  realizable := by {
    apply Exists.intro 0
    apply And.intro
    {
      exact Finset.mem_insert_self 0 {1}
    }
    {
      intro x
      exact rfl
    }
  }
}


-- #check Finset.min'
-- #check Finset.min

-- -- #eval (3, 5).1

-- noncomputable
-- def empirical_risk (h : H)
--                    (sample : List X)
--                    (H_set : Finset H)
--                    (loss : X → H → ℝ)
--                    (hinhset : h ∈ H_set) : ℝ :=
--   (1 / sample.length) * List.sum (sample.map (λ x => loss x h))


-- lemma map_of_nonempty_finset_nonempty {α β : Type} (f : α ↪ β)
--                                                   (s : Finset α):
--                                                   -- (hf : Function.Injective f)
--     s.Nonempty → (Finset.map f s).Nonempty :=
--   by
--     intro h
--     exact Finset.Nonempty.map h

-- def ERM (H_set : Finset H) (Hnonempty : Nonempty Hset) (sample : List X) (loss : X → H → ℝ) : H :=
--   sorry
--   -- have risk_pair := H_set.map (
--   -- have min_risk := Finset.min' risk_pair (λ p => p.2)
--   -- sorry
-- -- H_set.argmin (λ h => empirical_risk h sample H_set loss)

-- -- noncomputable
-- def iid_sample (D : X → ℝ) (m : ℕ) [Inhabited X] : List X :=
--   List.replicate m

-- structure PACLearnable :=
-- (X : Type)                    -- Instance space
-- (H : Type)                    -- Hypothesis space
-- (H_set : Finset H)            -- Finite hypothesis space
-- (D : X → ℝ)                   -- True distribution
-- (ε δ : ℝ)                     -- Accuracy and confidence
-- (sample_complexity : ℕ)       -- Minimum number of samples
-- (bound : ∀ m ≥ sample_complexity,
--   ∀ h ∈ H_set,
--     empirical_risk h (iid_sample D m).samples H_set loss ≤ ε ∧
--     ∃ h_good ∈ H_set, loss (iid_sample D m).samples h_good = 0)

-- -- Checking MeasureTheory and ProbabilityTheory are imported
-- variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
-- #check [IsProbabilityMeasure P]

-- variable {a b : ℝ≥0∞}
-- def m := RandG ℝ
-- #check Random Rand ℝ≥0∞
-- -- #eval Rand.next

-- #check m

end fallacyFormalization


-- #eval Lean.versionString
