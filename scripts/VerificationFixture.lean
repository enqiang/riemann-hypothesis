import Lib.ClassField.Places.DecompositionCompletion

open New Set

section

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Algebra K Ω]
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]

include K in
example (ι : Ω →+* PadicAlgCl p) {σ : Γ}
    (hσ : σ ∈ decompGroup Γ ((intQpBar p).comap ι)) (x : Ω) :
    ‖ι (σ • x)‖ = ‖ι x‖ :=
  congrArg (fun r : NNReal ↦ (r : ℝ)) ((mem_decompGroup_iff_nnnorm_eq (K := K) ι).mp hσ x)

include K in
example (ι : Ω →+* PadicAlgCl p) {σ : Γ}
    (hσ : ∀ x : Ω, ‖ι (σ • x)‖₊ = ‖ι x‖₊) :
    σ ∈ decompGroup Γ ((intQpBar p).comap ι) :=
  (mem_decompGroup_iff_nnnorm_eq (K := K) ι).mpr hσ

include K in
example (ι : Ω →+* PadicAlgCl p) {σ : Γ}
    (hσ : σ ∈ decompGroup Γ ((intQpBar p).comap ι)) {x : Ω}
    (hx : ι x ∈ closure (range (ι.comp (algebraMap K Ω)))) : σ • x = x :=
  smul_eq_self_of_mem_decompGroup_of_mem_closure (K := K) ι hσ hx

#print axioms New.mem_decompGroup_iff_nnnorm_eq

end
