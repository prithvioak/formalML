import Proj.defs
open defs

namespace loss

-- Proving convexity of squared loss

------------------------------ RELEVANT LEMMAS ---------------------------------
lemma sq_of_dec (α : ℚ) (h : 0 ≤ α ∧ α ≤ 1) : α^2 ≤ α :=
  by
  apply sq_le h.left h.right


lemma hproof (x1 x2 α : ℚ) (hα : 0 ≤ α ∧ α ≤ 1) :
  α * x1^2 + (1 - α) * x2^2 - (α * x1 + (1 - α) * x2)^2 ≥ 0 :=
  by
  let hend : (α * x1 + (1 - α) * x2)^2 = α^2 * x1^2 + 2 * α * (1 - α) * x1 * x2 + (1 - α)^2 * x2^2 := by ring
  rw [hend]
  calc
    _ = α * x1 ^ 2 + (1 - α) * x2 ^ 2 - α ^ 2 * x1 ^ 2 - 2 * α * (1 - α) * x1 * x2 - (1 - α) ^ 2 * x2 ^ 2 := by ring
    _ = α * x1 ^ 2 - α ^ 2 * x1 ^ 2 + (1 - α) * x2 ^ 2 - (1 - α) ^ 2 * x2 ^ 2 - 2 * α * (1 - α) * x1 * x2 := by ring
    _ = (α - α ^ 2) * x1 ^ 2 + (1 - α) * x2 ^ 2 - (1 - α) ^ 2 * x2 ^ 2 - 2 * α * (1 - α) * x1 * x2 := by ring
    _ = α * (1 - α) * x1 ^ 2 + (1 - α) * x2 ^ 2 - (1 - α) ^ 2 * x2 ^ 2 - 2 * α * (1 - α) * x1 * x2 := by ring
    _ = α * (1 - α) * x1 ^ 2 + ((1 - α) - (1 - α) ^ 2) * x2 ^ 2 - 2 * α * (1 - α) * x1 * x2 := by ring
    _ = α * (1 - α) * x1 ^ 2 + (1 - α) * (1 - (1 - α)) * x2 ^ 2 - 2 * α * (1 - α) * x1 * x2 := by ring
    _ = α * (1 - α) * x1 ^ 2 + (1 - α) * α * x2 ^ 2 - 2 * α * (1 - α) * x1 * x2 := by ring
    _ = α * (1 - α) * (x1 ^ 2 + x2 ^ 2 - 2 * x1 * x2) := by ring
    _ = α * (1 - α) * (x1 - x2) ^ 2 := by ring
    _ ≥ 0 :=
      by
      let hαpos : 0 ≤ α := hα.left
      let h1αpos : 0 ≤ 1 - α := by linarith
      let hppos : 0 ≤ (x1 - x2) ^ 2 := by exact sq_nonneg (x1 - x2)
      exact mul_nonneg (mul_nonneg hαpos h1αpos) hppos

-- Showing Jensen's inequality for quadratic functions!
lemma jensen_quadratic (x1 x2 α : ℚ) (hα : 0 ≤ α ∧ α ≤ 1):
  (α * x1 + (1 - α) * x2)^2 ≤ α * x1^2 + (1 - α) * x2^2 :=
  by
  let hproof := hproof x1 x2 α hα
  exact
    (Rat.le_iff_sub_nonneg ((α * x1 + (1 - α) * x2) ^ 2) (α * x1 ^ 2 + (1 - α) * x2 ^ 2)).mpr hproof

-------------------------------- PROOF -----------------------------------------

-- Applying Jensen's inequality to squared loss, we get convexity
theorem squared_loss_convex:
  ∀ (α p1 p2 label: ℚ), 0 ≤ α ∧ α ≤ 1 → squared_loss (α * p1 + (1 - α) * p2) label ≤ α * squared_loss p1 label + (1 - α) * squared_loss p2 label :=
  by
  intro α p1 p2 label hα
  rw [squared_loss, squared_loss, squared_loss]
  let hjen := jensen_quadratic (p1 - label) (p2 - label) α hα
  let hsub : (α * (p1 - label) + (1 - α) * (p2 - label)) = α * p1 + (1 - α) * p2 - label :=
    by
    calc
      _ = α * p1 + α * (-label) + (1 - α) * p2 + (1 - α) * (-label) := by linarith
      _ = α * p1 - α * label + (1 - α) * p2 + (1 - α) * (-label) := by linarith
      _ = α * p1 - α * label + (1 - α) * p2 - label + α * label := by linarith
      _ = α * p1 + (1 - α) * p2 - label := by linarith
  rw [hsub] at hjen
  exact hjen


end loss


-- Previous (unsuccessful) proof attempts
-- theorem squared_loss_convex:
--   ∀ (α p1 p2 label: ℚ), 0 ≤ α ∧ α ≤ 1 → squared_loss (α * p1 + (1 - α) * p2) label ≤ α * squared_loss p1 label + (1 - α) * squared_loss p2 label :=
--   by
--     intro α p1 p2 label hα
--     rw [squared_loss, squared_loss, squared_loss]
--     let lhs := (α * p1 + (1 - α) * p2 - label) ^ 2
--     let rhs := α * (p1 - label) ^ 2 + (1 - α) * (p2 - label) ^ 2
--     have lhs_expand : lhs = α^2 * (p1 - label)^2 + (1 - α)^2 * (p2 - label)^2 + 2 * α * (1 - α) * (p1 - label) * (p2 - label) := by ring
--     -- Expand the left-hand side (LHS)
--     have key_inequality : 2 * α * (1 - α) * (p1 - label) * (p2 - label) ≤ 0 := by
--     -- 2 * α * (1 - α) is non-negative because 0 ≤ α ≤ 1
--       apply mul_nonpos_of_nonneg_of_nonpos
--       { apply mul_nonneg
--         {
--           let hhelp : 0 ≤ (1 - α) := by simp [hα.right]
--           let haa' : 0 ≤ α * (1 - α) := mul_nonneg hα.left hhelp
--           linarith
--         }
--         {
--           sorry
--         }
--       }
--       { sorry }

--     calc
--       _ = α^2 * (p1 - label)^2 + (1 - α)^2 * (p2 - label)^2 + 2 * α * (1 - α) * (p1 - label) * (p2 - label) := by apply lhs_expand
--       _ ≤ α^2 * (p1 - label)^2 + (1 - α)^2 * (p2 - label)^2 := by linarith
--       _ ≤ rhs :=
--         by
--         let haasq : α ^ 2 ≤ α := by apply sq_of_dec α hα
--         let hα' : 0 ≤ 1 - α ∧ 1 - α ≤ 1 := And.intro (by linarith) (by linarith)
--         let h1asq : (1 - α) ^ 2 ≤ 1 - α := by apply sq_of_dec (1 - α) hα'
--         let hppos : 0 ≤ (p1 - label) ^ 2 := by exact sq_nonneg (p1 - label)
--         let hppos' : 0 ≤ (p2 - label) ^ 2 := by exact sq_nonneg (p2 - label)
--         let h1 : α^2 * (p1 - label)^2 ≤ α * (p1 - label)^2 := by
--           exact mul_le_mul_of_nonneg_right haasq hppos
--         let h2 : (1 - α)^2 * (p2 - label)^2 ≤ (1 - α) * (p2 - label)^2 := by
--           exact mul_le_mul_of_nonneg_right h1asq hppos'
--         exact add_le_add h1 h2
