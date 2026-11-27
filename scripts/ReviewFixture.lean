import Lib.General.LinearAlgebra.PolarDecomposition

open Matrix New

-- Keep the existing complex statement available by specialization, including arbitrary weights.
example {n k α : Type*} [Fintype n] [Fintype k] [DecidableEq k] [LinearOrder α]
    (wt : k → α) {X : Matrix n k ℂ} (hX : HasLeftInv X) :
    ∃ b : GL k ℂ, b.val.BlockTriangular wt ∧ (X * b.val)ᴴ * (X * b.val) = 1 :=
  exists_orthonormal_mul wt hX

-- A rectangular real frame can use a reversed weight order to obtain a lower triangular factor.
example {X : Matrix (Fin 3) (Fin 2) ℝ} (hX : HasLeftInv X) :
    ∃ b : GL (Fin 2) ℝ, (∀ i j, i < j → b.val i j = 0) ∧
      (X * b.val)ᴴ * (X * b.val) = 1 := by
  obtain ⟨b, h_tri, h_orth⟩ := exists_orthonormal_mul (OrderDual.toDual : Fin 2 → (Fin 2)ᵒᵈ) hX
  exact ⟨b, fun i j h ↦ h_tri (show OrderDual.toDual j < OrderDual.toDual i from h), h_orth⟩

-- A zero-column real frame is also allowed by the same statement.
example {X : Matrix (Fin 3) (Fin 0) ℝ} (hX : HasLeftInv X) :
    ∃ b : GL (Fin 0) ℝ, b.val.BlockTriangular (id : Fin 0 → Fin 0) ∧
      (X * b.val)ᴴ * (X * b.val) = 1 :=
  exists_orthonormal_mul id hX

#print axioms New.exists_orthonormal_mul
