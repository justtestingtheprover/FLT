import FLT.Mathlib.Algebra.IsQuaternionAlgebra
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Instances.Matrix
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.Hacks.RightActionInstances
import FLT.NumberField.Completion.Finite
/-!

# Definitions of various compact open subgrups of Dˣ and GL₂(𝔸_F^∞)

We define U₁(v) as a subgroup of GL₂(Fᵥ), and U₁(S) as a subgroup
of GL₂(𝔸_F^∞). We introduce the concept
of a rigidification `r : (D ⊗[F] 𝔸_F^∞) ≅ M₂(𝔸_F^∞)` in order
to push U₁(S) over to a subgroup of `(D ⊗[F] 𝔸_F^∞)ˣ`.

-/
variable (F : Type*) [Field F] [NumberField F] --[NumberField.IsTotallyReal F]

variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

open IsDedekindDomain

open scoped NumberField TensorProduct

namespace IsQuaternionAlgebra.NumberField

open scoped TensorProduct.RightActions in
/--
A rigidification of a quaternion algebra D over a number field F
is a fixed choice of `𝔸_F^∞`-algebra isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`. In other
words, it is a choice of splitting of `D ⊗[F] Fᵥ` (i.e. an isomorphism to `M₂(Fᵥ)`)
for all finite places `v` together with a guarantee that the isomorphism works
on the integral level at all but finitely many places. Such a rigidification exists
if and only if F is unramified at all finite places.
-/
abbrev Rigidification :=
    (D ⊗[F] (FiniteAdeleRing (𝓞 F) F) ≃ₐ[FiniteAdeleRing (𝓞 F) F]
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))

/--
A quaternion algebra over a number field is unramified if it is split
at all finite places. This is implemented as the existence of a rigidification
of `D`, that is, an isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`.
-/
def IsUnramified : Prop := Nonempty (Rigidification F D)

end IsQuaternionAlgebra.NumberField

open IsQuaternionAlgebra.NumberField IsDedekindDomain

variable {F}

namespace IsDedekindDomain

/-- `M_2(O_v)` as a subring of `M_2(F_v)`. -/
noncomputable def M2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subring (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :=
  (v.adicCompletionIntegers F).matrix

/-- `GL₂(𝒪ᵥ)` as a subgroup of `GL₂(Fᵥ)`. -/
noncomputable def GL2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) :=
  MonoidHom.range (Units.map
    (RingHom.mapMatrix (v.adicCompletionIntegers F).subtype).toMonoidHom)

theorem M2.localFullLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (M2.localFullLevel v).carrier :=
  (NumberField.isOpenAdicCompletionIntegers F v).matrix

theorem M2.localFullLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (M2.localFullLevel v).carrier :=
  (isCompact_iff_compactSpace.mpr (NumberField.instCompactSpaceAdicCompletionIntegers F v)).matrix

-- the clever way to prove this is a theorem of the form "if A is an open submonoid of R
-- then Aˣ is an open subgroup of Rˣ"
theorem GL2.localFullLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (GL2.localFullLevel v).carrier := by
  have ind : Topology.IsInducing (Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) :=
    Units.isInducing_embedProduct
  rw [ind.isOpen_iff]
  let S := (M2.localFullLevel v).carrier
  let Sop := MulOpposite.op '' S
  use S ×ˢ Sop
  constructor
  · apply IsOpen.prod (M2.localFullLevel.isOpen v)
    exact MulOpposite.opHomeomorph.isOpen_image.mpr (M2.localFullLevel.isOpen v)
  · ext u
    simp only [Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply]
    constructor
    · intro ⟨hval, hinv⟩
      rw [Set.mem_image] at hinv
      obtain ⟨inv_mat, hinv_mem, hinv_eq⟩ := hinv
      have hinv_eq' : inv_mat = u.inv := MulOpposite.op_injective hinv_eq
      simp only [GL2.localFullLevel, Subgroup.mem_carrier, MonoidHom.mem_range]
      let yval : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
        Matrix.of (fun i j => ⟨u.val i j, hval i j⟩)
      let yinv : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
        Matrix.of (fun i j => ⟨u.inv i j, hinv_eq' ▸ hinv_mem i j⟩)
      have hinj : Function.Injective 
          ((v.adicCompletionIntegers F).subtype.mapMatrix : 
           Matrix (Fin 2) (Fin 2) _ →+* Matrix (Fin 2) (Fin 2) _) := 
        Matrix.map_injective Subtype.val_injective
      have hyval : (v.adicCompletionIntegers F).subtype.mapMatrix yval = u.val := by
        ext i j; simp only [yval, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]; rfl
      have hyinv : (v.adicCompletionIntegers F).subtype.mapMatrix yinv = u.inv := by
        ext i j; simp only [yinv, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]; rfl
      have hmul : yval * yinv = 1 := by
        apply hinj
        rw [RingHom.map_mul, RingHom.map_one, hyval, hyinv]
        exact u.val_inv
      have hmul' : yinv * yval = 1 := by
        apply hinj
        rw [RingHom.map_mul, RingHom.map_one, hyval, hyinv]
        exact u.inv_val
      refine ⟨⟨yval, yinv, hmul, hmul'⟩, ?_⟩
      ext i j
      simp only [Units.coe_map, RingHom.mapMatrix_apply, Matrix.map_apply, yval, Matrix.of_apply]
      rfl
    · intro hu
      simp only [GL2.localFullLevel, Subgroup.mem_carrier, MonoidHom.mem_range] at hu
      obtain ⟨y, hy⟩ := hu
      constructor
      · intro i j
        have huval : u.val = (v.adicCompletionIntegers F).subtype.mapMatrix y.val := by
          have h := congr_arg Units.val hy
          simp only [Units.coe_map] at h
          exact h.symm
        rw [huval]
        exact (y.val i j).property
      · rw [Set.mem_image]
        refine ⟨(v.adicCompletionIntegers F).subtype.mapMatrix y.inv, ?_, ?_⟩
        · intro i j
          exact (y.inv i j).property
        · congr 1
          have huinv : u.inv = (v.adicCompletionIntegers F).subtype.mapMatrix y.inv := by
            calc u.inv = (Units.map (v.adicCompletionIntegers F).subtype.mapMatrix.toMonoidHom y).inv := by rw [← hy]
              _ = (v.adicCompletionIntegers F).subtype.mapMatrix y.inv := rfl
          exact huinv.symm

-- the clever way to prove this is a theorem of the form "if A is a compact submonoid of R
-- then Aˣ is a compact subgroup of Rˣ"
theorem GL2.localFullLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GL2.localFullLevel v).carrier :=
  sorry

lemma GL2.mem_localFullLevel {v : HeightOneSpectrum (𝓞 F)} {x : GL (Fin 2) (v.adicCompletion F)}
    (hx : x ∈ localFullLevel v) :
    ∃ x' : GL (Fin 2) (v.adicCompletionIntegers F),
      Units.map ((v.adicCompletionIntegers F).subtype.mapMatrix.toMonoidHom) x' = x :=
  hx

lemma GL2.mem_localFullLevel' {v : HeightOneSpectrum (𝓞 F)} {x : GL (Fin 2) (v.adicCompletion F)}
    (hx : x ∈ localFullLevel v) :
    ∃ x' : GL (Fin 2) (v.adicCompletionIntegers F), ∀ i j, x' i j = x i j := by
  refine (mem_localFullLevel hx).imp ?_
  simp only [RingHom.toMonoidHom_eq_coe, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply]
  rintro y hy
  simp [← hy]

lemma GL2.v_det_val_mem_localFullLevel_eq_one {v : HeightOneSpectrum (𝓞 F)}
    {x : GL (Fin 2) (v.adicCompletion F)} (hx : x ∈ localFullLevel v) :
    Valued.v x.val.det = 1 := by
  obtain ⟨y, hy⟩ := mem_localFullLevel hx
  have hd : IsUnit y.det.val := by simp
  rw [Valued.isUnit_valuationSubring_iff] at hd
  simpa [← hy, Matrix.det_fin_two] using hd

lemma GL2.v_le_one_of_mem_localFullLevel (v : HeightOneSpectrum (𝓞 F)) {x}
    (hx : x ∈ localFullLevel v) (i j) : Valued.v (x i j) ≤ 1 := by
  simp only [localFullLevel, Units.map, RingHom.mapMatrix, Matrix.map, ValuationSubring.subtype,
    Subring.subtype, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.toMonoidHom_eq_coe,
    RingHom.coe_monoidHom_mk, Units.inv_eq_val_inv, Matrix.coe_units_inv, MonoidHom.mem_range,
    MonoidHom.mk'_apply, Matrix.GeneralLinearGroup.ext_iff, Matrix.of_apply] at hx
  obtain ⟨x', hx'⟩ := hx
  simp only [← hx', ← HeightOneSpectrum.mem_adicCompletionIntegers, SetLike.coe_mem]

lemma GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one {v : HeightOneSpectrum (𝓞 F)}
    {x : GL (Fin 2) (v.adicCompletion F)} :
    x ∈ localFullLevel v ↔ (∀ (i j), Valued.v (x i j) ≤ 1) ∧ Valued.v x.val.det = 1 :=
  ⟨fun h ↦ ⟨GL2.v_le_one_of_mem_localFullLevel _ h, GL2.v_det_val_mem_localFullLevel_eq_one h⟩, by
    intro ⟨h₁, h₂⟩
    let M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
      Matrix.of fun i j => ⟨x i j, h₁ i j⟩
    have det_eq : M.det = x.val.det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]; simp [M]
    have isUnit_M :=
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Valued.isUnit_valuationSubring_iff.mpr (det_eq ▸ h₂)))
    use isUnit_M.unit
    ext i j; fin_cases i; all_goals fin_cases j
    all_goals simp [M]
  ⟩

open Valued

/-- local U_1(v), defined as a subgroup of GL₂(Fᵥ) given by
matrices in GL₂(𝒪ᵥ) congruent to (a *;0 a) mod v. -/
noncomputable def GL2.localTameLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) where
  carrier := {x ∈ localFullLevel v |
    Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧ Valued.v (x.val 1 0) < 1}
  mul_mem' {a b} ha hb := by
    simp_all only [Set.mem_setOf_eq, Units.val_mul]
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_, ?_⟩
    · simp only [Matrix.mul_apply, Fin.isValue, Fin.sum_univ_two]
      convert_to Valued.v ((a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1) +
        (a.val 0 1 * b.val 1 0 - a.val 1 0 * b.val 0 1)) < 1
      · ring_nf
      suffices Valued.v (a.val 0 1 * b.val 1 0) < 1 ∧
                Valued.v (a.val 1 0 * b.val 0 1) < 1 ∧
                Valued.v (a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1) < 1 by
        apply Valuation.map_add_lt _ this.2.2 ?_
        apply Valuation.map_sub_lt _ this.1 this.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [map_mul, mul_comm]
        apply mul_lt_one_of_lt_of_le hb.2.2
        apply v_le_one_of_mem_localFullLevel _ ha.1
      · rw [map_mul]
        apply mul_lt_one_of_lt_of_le ha.2.2
        apply v_le_one_of_mem_localFullLevel _ hb.1
      · convert_to Valued.v (a.val 0 0 * (b.val 0 0 - b.val 1 1) +
          (a.val 0 0 - a.val 1 1) * b.val 1 1) < 1
        · ring_nf
        apply Valuation.map_add_lt _
        · rw [map_mul, mul_comm]
          apply mul_lt_one_of_lt_of_le hb.2.1
          apply v_le_one_of_mem_localFullLevel _ ha.1
        · rw [map_mul]
          apply mul_lt_one_of_lt_of_le ha.2.1
          apply v_le_one_of_mem_localFullLevel _ hb.1
    · simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two]
      apply Valuation.map_add_lt _
      · rw [map_mul]
        apply mul_lt_one_of_lt_of_le ha.2.2
        apply v_le_one_of_mem_localFullLevel _ hb.1
      · rw [map_mul, mul_comm]
        apply mul_lt_one_of_lt_of_le hb.2.2
        apply v_le_one_of_mem_localFullLevel _ ha.1
  one_mem' := by simp [one_mem]
  inv_mem' {a} ha := by
    simp_all only [Set.mem_setOf_eq, inv_mem_iff, Matrix.coe_units_inv, true_and,
      Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two,
      Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, smul_eq_mul, Matrix.cons_val_one,
      ← mul_sub, map_mul, map_inv₀, mul_neg, Valuation.map_neg]
    rw [Valuation.map_sub_swap, v_det_val_mem_localFullLevel_eq_one ha.1]
    simp [ha.2]

/-- The local tame level `U₁(v)` is a subgroup of the local full level `GL₂(𝒪ᵥ)`. -/
lemma GL2.localTameLevel_le_localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    localTameLevel v ≤ localFullLevel v := by
  intro x hx
  exact hx.1

/-- Membership in the local tame level `U₁(v)` can be characterized purely in terms of
valuations: an element of `GL₂(Fᵥ)` lies in `U₁(v)` if and only if all entries have
valuation at most 1, the determinant has valuation exactly 1, the diagonal entries are
congruent modulo `v`, and the lower-left entry has valuation strictly less than 1. -/
theorem GL2.mem_localTameLevel_iff {v : HeightOneSpectrum (𝓞 F)}
    {x : GL (Fin 2) (v.adicCompletion F)} :
    x ∈ localTameLevel v ↔
      (∀ i j, Valued.v (x.val i j) ≤ 1) ∧ Valued.v x.val.det = 1 ∧
      Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧ Valued.v (x.val 1 0) < 1 := by
  simp only [localTameLevel, Subgroup.mem_mk, Set.mem_setOf_eq,
    mem_localFullLevel_iff_v_le_one_and_v_det_eq_one]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2⟩, h3, h4⟩

-- the clever way to prove this is a theorem of the form "if A is an open submonoid of R
-- then Aˣ is an open subgroup of Rˣ"
theorem GL2.localTameLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (GL2.localTameLevel v).carrier := by
  have h1 : IsOpen (GL2.localFullLevel v).carrier := GL2.localFullLevel.isOpen v
  have h2 : IsOpen {x : GL (Fin 2) (v.adicCompletion F) | Valued.v (x.val 0 0 - x.val 1 1) < 1} := by
    have hball : IsOpen {x : v.adicCompletion F | Valued.v x < 1} := 
      Valued.isOpen_ball (R := v.adicCompletion F) 1
    refine IsOpen.preimage ?_ hball
    have hcont1 : Continuous (fun x : GL (Fin 2) (v.adicCompletion F) => x.val 0 0) :=
      Units.continuous_val.matrix_elem 0 0
    have hcont2 : Continuous (fun x : GL (Fin 2) (v.adicCompletion F) => x.val 1 1) :=
      Units.continuous_val.matrix_elem 1 1
    exact hcont1.sub hcont2
  have h3 : IsOpen {x : GL (Fin 2) (v.adicCompletion F) | Valued.v (x.val 1 0) < 1} := by
    have hball : IsOpen {x : v.adicCompletion F | Valued.v x < 1} := 
      Valued.isOpen_ball (R := v.adicCompletion F) 1
    refine IsOpen.preimage ?_ hball
    exact Units.continuous_val.matrix_elem 1 0
  have : (GL2.localTameLevel v).carrier = 
         (GL2.localFullLevel v).carrier ∩ 
         ({x | Valued.v (x.val 0 0 - x.val 1 1) < 1} ∩ {x | Valued.v (x.val 1 0) < 1}) := by
    ext x
    simp only [GL2.localTameLevel, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro ⟨hx1, hx2, hx3⟩
      exact ⟨hx1, hx2, hx3⟩
    · intro ⟨hx1, hx2, hx3⟩
      exact ⟨hx1, hx2, hx3⟩
  rw [this]
  exact h1.inter (h2.inter h3)

-- the clever way to prove this is a theorem of the form "if A is a compact submonoid of R
-- then Aˣ is a compact subgroup of Rˣ"
theorem GL2.localTameLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GL2.localTameLevel v).carrier :=
  sorry

end IsDedekindDomain

open RestrictedProduct

/-- The canonical F-algebra morphism from `𝔸_F^∞` (the finite adeles of a number field F) to
the local component `F_v` for `v` a finite place of `𝓞 F`. -/
noncomputable
def IsDedekindDomain.FiniteAdeleRing.toAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] HeightOneSpectrum.adicCompletion F v where
  __ := RestrictedProduct.evalRingHom _ v
  commutes' _ := rfl

namespace IsDedekindDomain.FiniteAdeleRing

/-- The canonical group homomorphism from `GL_2(𝔸_F^∞)` to the local component `GL_2(F_v)` for `v`
a finite place. -/
noncomputable def GL2.toAdicCompletion
    (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →*
    GL (Fin 2) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (FiniteAdeleRing.toAdicCompletion v)).toMonoidHom

/-- `GL_2(𝔸_F^∞)` is isomorphic and homeomorphic to the
restricted product of the local components `GL_2(F_v)`.
-/
noncomputable def GL2.restrictedProduct :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ≃ₜ*
    Πʳ (v : HeightOneSpectrum (𝓞 F)),
      [(GL (Fin 2) (v.adicCompletion F)), (M2.localFullLevel v).units] :=
  ContinuousMulEquiv.restrictedProductMatrixUnits (NumberField.isOpenAdicCompletionIntegers F)

end IsDedekindDomain.FiniteAdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing

/-- If `F` is a number field and `S` is a finite set of finite places of `𝓞 F` then
`GL2.TameLevel S` is the subgroup of `GL₂(𝔸_F^∞)` consisting of things in `GL₂(𝓞ᵥ)` for
all places, and furthermore in the local "`U₁(v)`" subgroup `(a *;0 a) mod v` for all `v ∈ S`.
-/
noncomputable def GL2.TameLevel (S : Finset (HeightOneSpectrum (𝓞 F))) :
  Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) where
    carrier := {x | (∀ v, GL2.toAdicCompletion v x ∈ GL2.localFullLevel v) ∧
      (∀ v ∈ S, GL2.toAdicCompletion v x ∈ GL2.localTameLevel v)}
    mul_mem' {a b} ha hb := by simp_all [mul_mem]
    one_mem' := by simp_all [one_mem]
    inv_mem' {x} hx := by simp_all

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem GL2.TameLevel.isOpen : IsOpen (GL2.TameLevel S).carrier :=
  sorry

theorem GL2.TameLevel.isCompact : IsCompact (GL2.TameLevel S).carrier :=
  sorry

open scoped TensorProduct.RightActions in
/-- The subgroup of `(D ⊗ 𝔸_F^∞)ˣ` corresponding to the subgroup `U₁(S)` of `GL₂(𝔸_F^∞)`
(that is, matrices congruent to `(a *; 0 a) mod v` for all `v ∈ S`) via the rigidification `r`. -/
noncomputable def QuaternionAlgebra.TameLevel (r : Rigidification F D) :
    Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  Subgroup.comap (Units.map r.toMonoidHom) (GL2.TameLevel S)

open scoped TensorProduct.RightActions in
theorem Rigidification.continuous_toFun (r : Rigidification F D) :
    Continuous r :=
  letI : ∀ (i : HeightOneSpectrum (𝓞 F)),
      Algebra (FiniteAdeleRing (𝓞 F) F) ((i.adicCompletion F)) :=
    fun i ↦ (RestrictedProduct.evalRingHom _ i).toAlgebra
  IsModuleTopology.continuous_of_linearMap r.toLinearMap

open scoped TensorProduct.RightActions in
theorem Rigidification.continuous_invFun (r : Rigidification F D) :
    Continuous r.symm := by
  haveI : ContinuousAdd (D ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))
  exact IsModuleTopology.continuous_of_linearMap r.symm.toLinearMap

end HeightOneSpectrum

end IsDedekindDomain
