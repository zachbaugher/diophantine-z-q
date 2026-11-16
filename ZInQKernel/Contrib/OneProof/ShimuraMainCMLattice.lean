import ZInQKernel.Contrib.OneProof.RingClassLattice

/-!
# hCM groundwork: the lattice-level glue of `T5Glue.ShimuraMainCM`

Claim: `Claiming hCM at 43513d873eb7ef246cc6f43575a659ff570a70b2` on issue #14. The hypothesis is the argument
`hCM : T5Glue.ShimuraMainCM` of `ZInQ.OneProof.frozenTarget` (Shimura 1971, Thm. 5.4, in Weierstrass coordinates).

**This file discharges nothing.** It proves three facts about the statement of `ShimuraMainCM` that a proof of it
can use, none of which is CM theory:

* everything the statement says about a period pair depends only on its lattice
  (`weierstrassP_eq_of_lattice_eq`, `derivWeierstrassP_eq_of_lattice_eq`, `g₂_eq_of_lattice_eq`,
  `g₃_eq_of_lattice_eq`, `isConjModel_congr`), so the quantifier over all `P`, `P'` with the prescribed lattices
  costs nothing (`conclusion_congr`);
* the bare `Set` `𝔞` of the statement is `κ⁻¹(Λ_P)`, a `ℤ`-submodule of `K` (`eq_kappaComap`), and
  `T5Glue.sInvLat m s 𝔞` is a `ℤ`-submodule of `K` too (`sInvLatSubgroup`);
* the conclusion does not depend on the representative `v` of `s⁻¹u` (`weierstrassP_rep_eq`,
  `derivWeierstrassP_rep_eq`), so it suffices to prove it for one representative of each `u`
  (`conclusion_of_one_rep`).

What stays open is Shimura's Theorem 5.4 itself and the classification of analytic isomorphisms
`ℂ/Λ → E(ℂ)`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.ShimuraMainCMLattice

open T5Glue ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-! ## §1. Only the lattice of a period pair matters -/

section Lattice

variable {P Q : PeriodPair}

theorem isScale_one_of_lattice_eq (h : P.lattice = Q.lattice) : IsScale P Q 1 :=
  ⟨one_ne_zero, by rw [h, one_smul]⟩

theorem weierstrassP_eq_of_lattice_eq (h : P.lattice = Q.lattice) (z : ℂ) :
    P.weierstrassP z = Q.weierstrassP z := by
  simpa using (isScale_one_of_lattice_eq h).weierstrassP z

theorem derivWeierstrassP_eq_of_lattice_eq (h : P.lattice = Q.lattice) (z : ℂ) :
    P.derivWeierstrassP z = Q.derivWeierstrassP z := by
  simpa using (isScale_one_of_lattice_eq h).derivWeierstrassP z

theorem g₂_eq_of_lattice_eq (h : P.lattice = Q.lattice) : P.g₂ = Q.g₂ := by
  simpa using (isScale_one_of_lattice_eq h).g₂

theorem g₃_eq_of_lattice_eq (h : P.lattice = Q.lattice) : P.g₃ = Q.g₃ := by
  simpa using (isScale_one_of_lattice_eq h).g₃

theorem isConjModel_congr (σ : ℂ →+* ℂ) {P P' Q Q' : PeriodPair} (hP : P.lattice = Q.lattice)
    (hP' : P'.lattice = Q'.lattice) (μ : ℂ) : IsConjModel σ P P' μ ↔ IsConjModel σ Q Q' μ := by
  simp only [IsConjModel, g₂_eq_of_lattice_eq hP, g₃_eq_of_lattice_eq hP, g₂_eq_of_lattice_eq hP',
    g₃_eq_of_lattice_eq hP']

end Lattice

/-! ## §2. `𝔞` and `s⁻¹𝔞` are `ℤ`-submodules of `K` -/

section Submodules

variable {m : ℕ} [NeZero m]

/-- If `Λ_P = κ(𝔞)`, then `𝔞 = κ⁻¹(Λ_P)`, a `ℤ`-submodule of `K`. -/
theorem eq_kappaComap {𝔞 : Set (QNeg m)} {P : PeriodPair} (h : (P.lattice : Set ℂ) = kappa m '' 𝔞) :
    𝔞 = ((kappaComap (m := m) P.lattice : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
  rw [coe_kappaComap, h, Set.preimage_image_eq _ kappa_injective]

/-- `s⁻¹M = {x ∈ K : s_f x ∈ M̂}` as an additive subgroup of `K`, for a `ℤ`-submodule `M ⊂ K`. -/
def sInvLatSubgroup (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (M : Submodule ℤ (QNeg m)) :
    AddSubgroup (QNeg m) where
  carrier := sInvLat m s (M : Set (QNeg m))
  zero_mem' := by
    show finPart s * algebraMap (QNeg m) (AfK m) 0 ∈ latHat m (M : Set (QNeg m))
    rw [map_zero, mul_zero, ← map_zero (algebraMap (QNeg m) (AfK m))]
    exact mem_latHat_of_mem M.zero_mem
  add_mem' := by
    intro x y hx hy
    show finPart s * algebraMap (QNeg m) (AfK m) (x + y) ∈ latHat m (M : Set (QNeg m))
    rw [map_add, mul_add]
    exact latHat_add_mem M hx hy
  neg_mem' := by
    intro x hx
    show finPart s * algebraMap (QNeg m) (AfK m) (-x) ∈ latHat m (M : Set (QNeg m))
    have h0 : (0 : AfK m) ∈ latHat m (M : Set (QNeg m)) := by
      rw [← map_zero (algebraMap (QNeg m) (AfK m))]
      exact mem_latHat_of_mem M.zero_mem
    rw [map_neg, mul_neg, (zero_sub (finPart s * algebraMap (QNeg m) (AfK m) x)).symm]
    exact latHat_sub_mem M h0 hx

theorem coe_sInvLatSubgroup (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (M : Submodule ℤ (QNeg m)) :
    ((sInvLatSubgroup s M : AddSubgroup (QNeg m)) : Set (QNeg m)) = sInvLat m s (M : Set (QNeg m)) :=
  rfl

/-- `s⁻¹M` as a `ℤ`-submodule of `K`. -/
def sInvLatSubmodule (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (M : Submodule ℤ (QNeg m)) :
    Submodule ℤ (QNeg m) :=
  (sInvLatSubgroup s M).toIntSubmodule

theorem coe_sInvLatSubmodule (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (M : Submodule ℤ (QNeg m)) :
    ((sInvLatSubmodule s M : Submodule ℤ (QNeg m)) : Set (QNeg m)) = sInvLat m s (M : Set (QNeg m)) :=
  rfl

end Submodules

/-! ## §3. Independence of the representative of `s⁻¹u` -/

section Rep

variable {m : ℕ} [NeZero m] {s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)} {𝔞 : Set (QNeg m)}
  {P P' : PeriodPair}

/-- Two representatives `v, v'` of `s⁻¹u` differ by an element of `s⁻¹𝔞`, so `κ(v) − κ(v') ∈ Λ_{P'}`. -/
theorem kappa_sub_mem_of_rep (hP : (P.lattice : Set ℂ) = kappa m '' 𝔞)
    (hP' : (P'.lattice : Set ℂ) = kappa m '' sInvLat m s 𝔞) {u v v' : QNeg m}
    (hv : finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞)
    (hv' : finPart s * algebraMap (QNeg m) (AfK m) v' - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞) :
    kappa m v - kappa m v' ∈ P'.lattice := by
  have hd : v - v' ∈ sInvLat m s 𝔞 := by
    show finPart s * algebraMap (QNeg m) (AfK m) (v - v') ∈ latHat m 𝔞
    have e : finPart s * algebraMap (QNeg m) (AfK m) (v - v') =
        (finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u) -
          (finPart s * algebraMap (QNeg m) (AfK m) v' - algebraMap (QNeg m) (AfK m) u) := by
      rw [map_sub]; ring
    have h𝔞 := eq_kappaComap hP
    rw [e]
    rw [h𝔞] at hv hv' ⊢
    exact latHat_sub_mem _ hv hv'
  rw [← kappa_sub, ← SetLike.mem_coe, hP']
  exact ⟨_, hd, rfl⟩

theorem weierstrassP_rep_eq (hP : (P.lattice : Set ℂ) = kappa m '' 𝔞)
    (hP' : (P'.lattice : Set ℂ) = kappa m '' sInvLat m s 𝔞) {u v v' : QNeg m}
    (hv : finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞)
    (hv' : finPart s * algebraMap (QNeg m) (AfK m) v' - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞) :
    P'.weierstrassP (kappa m v) = P'.weierstrassP (kappa m v') := by
  have h := kappa_sub_mem_of_rep hP hP' hv hv'
  have e : kappa m v = kappa m v' + (kappa m v - kappa m v') := by ring
  rw [e, P'.weierstrassP_add_coe _ ⟨_, h⟩]

theorem derivWeierstrassP_rep_eq (hP : (P.lattice : Set ℂ) = kappa m '' 𝔞)
    (hP' : (P'.lattice : Set ℂ) = kappa m '' sInvLat m s 𝔞) {u v v' : QNeg m}
    (hv : finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞)
    (hv' : finPart s * algebraMap (QNeg m) (AfK m) v' - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞) :
    P'.derivWeierstrassP (kappa m v) = P'.derivWeierstrassP (kappa m v') := by
  have h := kappa_sub_mem_of_rep hP hP' hv hv'
  have e : kappa m v = kappa m v' + (kappa m v - kappa m v') := by ring
  rw [e, P'.derivWeierstrassP_add_coe _ ⟨_, h⟩]

end Rep

/-! ## §4. The conclusion of `ShimuraMainCM`, and the two reductions -/

section Conclusion

variable {m : ℕ} [NeZero m]

/-- The conclusion of `ShimuraMainCM` for fixed `σ`, `s`, `𝔞`, `P`, `P'` (verbatim). -/
def Conclusion (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (𝔞 : Set (QNeg m))
    (P P' : PeriodPair) : Prop :=
  ∃ μ : ℂ, IsConjModel (σ : ℂ →+* ℂ) P P' μ ∧
    ∀ u v : QNeg m, kappa m u ∉ P.lattice →
      finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞 →
      σ (P.weierstrassP (kappa m u)) = μ ^ 2 * P'.weierstrassP (kappa m v) ∧
      σ (P.derivWeierstrassP (kappa m u)) = μ ^ 3 * P'.derivWeierstrassP (kappa m v)

/-- `ShimuraMainCM` is the statement that `Conclusion` holds for all its data (by `Iff.rfl`). -/
theorem shimuraMainCM_iff :
    ShimuraMainCM ↔
      ∀ (m : ℕ) [NeZero m], Squarefree m →
      ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
        ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
          I * (Real.sqrt m : ℂ) →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
      ∀ (𝔞 : Set (QNeg m)) (P P' : PeriodPair),
        (P.lattice : Set ℂ) = kappa m '' 𝔞 → (P'.lattice : Set ℂ) = kappa m '' sInvLat m s 𝔞 →
        Conclusion σ s 𝔞 P P' :=
  Iff.rfl

/-- The conclusion depends only on the lattices of `P` and `P'`. -/
theorem conclusion_congr {σ : ℂ ≃+* ℂ} {s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)} {𝔞 : Set (QNeg m)}
    {P P' Q Q' : PeriodPair} (hP : P.lattice = Q.lattice) (hP' : P'.lattice = Q'.lattice) :
    Conclusion σ s 𝔞 P P' ↔ Conclusion σ s 𝔞 Q Q' := by
  simp only [Conclusion, isConjModel_congr _ hP hP', hP, weierstrassP_eq_of_lattice_eq hP,
    derivWeierstrassP_eq_of_lattice_eq hP, weierstrassP_eq_of_lattice_eq hP',
    derivWeierstrassP_eq_of_lattice_eq hP']

/-- It suffices to prove the conclusion for one representative `v` of `s⁻¹u` for each `u ∉ 𝔞`. -/
theorem conclusion_of_one_rep {σ : ℂ ≃+* ℂ} {s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)} {𝔞 : Set (QNeg m)}
    {P P' : PeriodPair} (hP : (P.lattice : Set ℂ) = kappa m '' 𝔞)
    (hP' : (P'.lattice : Set ℂ) = kappa m '' sInvLat m s 𝔞) {μ : ℂ}
    (hμ : IsConjModel (σ : ℂ →+* ℂ) P P' μ)
    (h : ∀ u : QNeg m, kappa m u ∉ P.lattice → ∃ v : QNeg m,
      finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞 ∧
      σ (P.weierstrassP (kappa m u)) = μ ^ 2 * P'.weierstrassP (kappa m v) ∧
      σ (P.derivWeierstrassP (kappa m u)) = μ ^ 3 * P'.derivWeierstrassP (kappa m v)) :
    Conclusion σ s 𝔞 P P' := by
  refine ⟨μ, hμ, fun u v hu hv => ?_⟩
  obtain ⟨v₀, hv₀, h1, h2⟩ := h u hu
  rw [weierstrassP_rep_eq hP hP' hv hv₀, derivWeierstrassP_rep_eq hP hP' hv hv₀]
  exact ⟨h1, h2⟩

end Conclusion

end ZInQ.Contrib.ShimuraMainCMLattice
