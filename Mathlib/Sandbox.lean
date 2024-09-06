import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

section frontier

theorem frontier_union_subset' {X : Type*} [TopologicalSpace X] (s : Set X) (t : Set X) :
    frontier (s ∪ t) ⊆ frontier s ∪ frontier t :=
  (frontier_union_subset s t).trans <|
    Set.union_subset_union Set.inter_subset_left Set.inter_subset_right

theorem Finset.frontier_biUnion {ι : Type*} (s : Finset ι) {X : Type*} [TopologicalSpace X]
    (t : ι → Set X) :
    frontier (⋃ i ∈ s, t i) ⊆ ⋃ i ∈ s, frontier (t i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ h_ind =>
      simp_rw [mem_insert, Set.iUnion_iUnion_eq_or_left]
      exact (frontier_union_subset' _ _).trans ( Set.union_subset_union subset_rfl h_ind)

example {α β : Type*} (f : α → Set β) :
    ⋃ a, f a = ⋃ a ∈ Set.univ, f a := by
  exact Eq.symm (Set.biUnion_univ f)

theorem frontier_iUnion {ι : Type*} [Fintype ι] {X : Type*} [TopologicalSpace X]
    (t : ι → Set X) :
    frontier (⋃ i, t i) ⊆ ⋃ i, frontier (t i) := by
  have := Finset.frontier_biUnion Finset.univ t
  simp only [Finset.mem_univ, Set.iUnion_true] at this
  exact this

end frontier

section finset

@[simp]
theorem Finset.union_nonempty {α : Type*} [DecidableEq α] {s : Finset α}  {t : Finset α} :
    (s ∪ t : Finset α).Nonempty ↔ s.Nonempty ∨ t.Nonempty := by
  rw [← Finset.coe_nonempty, Finset.coe_union, Set.union_nonempty, coe_nonempty, coe_nonempty]

end finset

section rpow

theorem Real.rpow_comm {x : ℝ} (hx : 0 ≤ x)  (y z : ℝ) :
    (x ^ y) ^ z = (x ^ z) ^ y := by
  rw [← rpow_mul hx, ← rpow_mul hx, mul_comm]

end rpow

section ennreal

@[simp]
theorem ENNReal.coe_RealtoNNReal (r : ℝ) : (Real.toNNReal r : ENNReal) = ENNReal.ofReal r := rfl

theorem ENNReal.ofReal_ne_zero_iff {r : ℝ} :
    ENNReal.ofReal r ≠ 0 ↔ 0 < r := by
  rw [← zero_lt_iff, ENNReal.ofReal_pos]

end ennreal

section topo

theorem measurableSet_frontier {α : Type*} {s : Set α} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] :
    MeasurableSet (frontier s) :=
  measurableSet_closure.diff measurableSet_interior

end topo

section basis

variable {𝕜 : Type*} [hnorm : NontriviallyNormedField 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E] [CompleteSpace 𝕜] {ι : Type*}
  [Finite ι]  [T2Space E] (v : Basis ι 𝕜 E)

theorem Basis.equivFunL_coe :
  ⇑v.equivFunL = v.equivFun := rfl

theorem Basis.equivFunL_symm_coe :
  ⇑v.equivFunL.symm = v.equivFun.symm := rfl

end basis

section indicator

variable {α β : Type*} [One β] {f : α → β} {s : Set α}

@[to_additive]
theorem Set.eqOn_mulIndicator' : Set.EqOn (Set.mulIndicator s f) 1 sᶜ :=
  fun _ hx => mulIndicator_of_not_mem hx f

variable [TopologicalSpace α] [TopologicalSpace β]

open scoped Topology

@[to_additive]
theorem continuousAt_mulIndicator_of_not_mem_frontier (hf : ContinuousOn f (interior s))
    {x : α} (hx : x ∉ frontier s) :
    ContinuousAt (s.mulIndicator f) x := by
  rw [← Set.not_mem_compl_iff, Set.not_not_mem, compl_frontier_eq_union_interior] at hx
  obtain h | h := hx
  · have hs : interior s ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp (by rwa [interior_interior])
    exact ContinuousAt.congr (hf.continuousAt hs) <| Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨interior s, hs, Set.eqOn_mulIndicator.symm.mono interior_subset⟩
  · refine ContinuousAt.congr continuousAt_const <| Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨sᶜ, mem_interior_iff_mem_nhds.mp h, Set.eqOn_mulIndicator'.symm⟩

end indicator

section diff

theorem Set.eq_union_of_diff_subset {α : Type*} {s t u : Set α} (h : t ⊆ s) :
    s \ t = u → s = t ∪ u := by aesop

end diff

section Measure

open MeasureTheory MeasureTheory.Measure MeasurableSpace

theorem MeasureTheory.measure_restrict_pi_pi {ι : Type*} {α : ι → Type*} [Fintype ι]
    [(i : ι) → MeasurableSpace (α i)] (μ : (i : ι) → MeasureTheory.Measure (α i))
    [∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) :
    (Measure.pi μ).restrict (Set.univ.pi fun i ↦ s i) =
      Measure.pi (fun i ↦ (μ i).restrict (s i)) := by
  refine (Measure.pi_eq fun _ h ↦ ?_).symm
  simp_rw [restrict_apply (MeasurableSet.univ_pi h), restrict_apply (h _),
    ← Set.pi_inter_distrib, pi_pi]

section marginal

variable {δ : Type*} {π : δ → Type*} [DecidableEq δ] [(x : δ) → MeasurableSpace (π x)]
    {μ : (i : δ) → MeasureTheory.Measure (π i)} {s : Finset δ}

theorem Measurable.lmarginal_zero {x : (i : δ) → π i} :
    (∫⋯∫⁻_s, 0 ∂μ) x = 0 := lintegral_zero

theorem Measurable.lmarginal_update [∀ (i : δ), SigmaFinite (μ i)]
    {f : ((i : δ) → π i) → ENNReal} (hf : Measurable f) {x : (i : δ) → π i} {i : δ} :
    Measurable fun xᵢ ↦ (∫⋯∫⁻_s, f ∂μ) (Function.update x i xᵢ) := by
  exact (Measurable.lmarginal _ hf).comp (measurable_update x)

theorem MeasureTheory.lmarginal_const_smul
    {f : ((i : δ) → π i) → ENNReal} (hf : Measurable f) {x : (i : δ) → π i} (r : ENNReal) :
    (∫⋯∫⁻_s, r • f ∂μ) x = r * (∫⋯∫⁻_s, f ∂μ) x := by
  simp_rw [lmarginal, Pi.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul _ (by convert hf.comp measurable_updateFinset)]

theorem MeasureTheory.lmarginal_const_smul'
    {f : ((i : δ) → π i) → ENNReal} {x : (i : δ) → π i} (r : ENNReal) (hr : r ≠ ⊤):
    (∫⋯∫⁻_s, r • f ∂μ) x = r * (∫⋯∫⁻_s, f ∂μ) x := by
  simp_rw [lmarginal, Pi.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul' _ _ hr]

end marginal

theorem Complex.lintegral_pi_comp_polarCoord_symm_aux {ι : Type*} [DecidableEq ι]
    (f : (ι → ℂ) → ENNReal) (hf : Measurable f) (s : Finset ι) (a : ι → ℝ × ℝ) :
    (∫⋯∫⁻_s, f ∂fun _ ↦ (volume : Measure ℂ)) (fun i ↦ Complex.polarCoord.symm (a i)) =
      (∫⋯∫⁻_s, fun p ↦
          ((∏ i ∈ s, (p i).1.toNNReal) * f (fun i ↦ Complex.polarCoord.symm (p i)))
            ∂fun _ ↦ ((volume : Measure (ℝ × ℝ)).restrict polarCoord.target)) a := by
  induction s using Finset.induction generalizing f a with
  | empty => simp
  | @insert i₀ s hi₀ h_ind =>
      have h : ∀ t : Finset ι, Measurable fun p : ι → ℝ × ℝ ↦
          (∏ i ∈ t, (p i).1.toNNReal) * f fun i ↦ Complex.polarCoord.symm (p i) := by
        intro _
        refine Measurable.mul ?_ ?_
        · exact measurable_coe_nnreal_ennreal_iff.mpr <|
            Finset.measurable_prod _ fun _ _ ↦ by fun_prop
        · exact hf.comp <| measurable_pi_lambda _ fun _ ↦
            Complex.continuous_polarCoord_symm.measurable.comp (measurable_pi_apply _)
      calc
        _ = ∫⁻ x in polarCoord.target, x.1.toNNReal •
              (∫⋯∫⁻_s, f ∂fun _ ↦ volume)
                fun j ↦ Complex.polarCoord.symm (Function.update a i₀ x j) := by
          rw [MeasureTheory.lmarginal_insert _ hf hi₀, ← Complex.lintegral_comp_polarCoord_symm _
            hf.lmarginal_update]
          congr!
          simp_rw [Function.update_apply]
          split_ifs <;> rfl
        _ = ∫⁻ (x : ℝ × ℝ) in polarCoord.target,
              (∫⋯∫⁻_s,
                (fun p ↦ ↑(∏ i ∈ insert i₀ s, (p i).1.toNNReal) *
                  (f fun i ↦ Complex.polarCoord.symm (p i))) ∘ fun p ↦ Function.update p i₀ x
              ∂fun _ ↦ volume.restrict polarCoord.target) a := by
            simp_rw [h_ind _ hf, lmarginal_update_of_not_mem (h s) hi₀, Function.comp_def,
              ENNReal.smul_def, smul_eq_mul, ← lmarginal_const_smul' _ ENNReal.coe_ne_top,
              Pi.smul_def, Finset.prod_insert hi₀, Function.update_same, smul_eq_mul,
              ENNReal.coe_mul, mul_assoc]
        _ = (∫⋯∫⁻_insert i₀ s, fun p ↦ (∏ i ∈ insert i₀ s, (p i).1.toNNReal) *
              f (fun i ↦ Complex.polarCoord.symm (p i))
                ∂fun _ ↦ volume.restrict polarCoord.target) a := by
          simp_rw [← lmarginal_update_of_not_mem (h _) hi₀]
          rw [MeasureTheory.lmarginal_insert _ (h _) hi₀]

theorem Complex.lintegral_pi_comp_polarCoord_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℂ) → ENNReal) (hf : Measurable f) :
    ∫⁻ p, f p = ∫⁻ p in (Set.univ.pi fun _ : ι ↦ polarCoord.target),
      (∏ i, (p i).1.toNNReal) * f (fun i ↦ Complex.polarCoord.symm (p i)) := by
  rw [volume_pi, lintegral_eq_lmarginal_univ (fun _ ↦ Complex.polarCoord.symm 0),
    Complex.lintegral_pi_comp_polarCoord_symm_aux _ hf, lmarginal_univ, ← measure_restrict_pi_pi]
  rfl

/-- A family of algebra homomorphisms `g i : A →ₐ[R] B i` defines an algebra homomorphism
`Pi.algHom f : A →+* Π i, B i` given by `Pi.algHom f x i = f i x`. -/
@[simps!]
def Pi.algHom {I R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A] {B : I → Type*}
    [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)] (g : (i : I) → A →ₐ[R] B i) :
    A →ₐ[R] (i : I) → B i where
  __ := Pi.ringHom fun i ↦ (g i)
  commutes' _ := by ext; simp

theorem Equiv.arrowProdEquivProdArrow_preimage {α β γ : Type*} {s : γ → Set α} {t : γ → Set β} :
    Equiv.arrowProdEquivProdArrow α β γ ⁻¹' (_root_.Set.univ.pi s ×ˢ _root_.Set.univ.pi t) =
      (_root_.Set.univ.pi fun i ↦ s i ×ˢ t i) := by
  ext
  simp only [arrowProdEquivProdArrow, coe_fn_mk, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, true_implies, forall_and]

def MeasurableEquiv.arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α]
    [MeasurableSpace β] :
    (γ → α × β) ≃ᵐ (γ → α) × (γ → β) where
  __ := Equiv.arrowProdEquivProdArrow α β γ
  measurable_toFun _ h := by
    simp_rw [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk]
    exact MeasurableSet.preimage h (by fun_prop)
  measurable_invFun _ h := by
    simp_rw [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    exact MeasurableSet.preimage h (by fun_prop)

theorem MeasurePreserving.arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α]
    [MeasurableSpace β] [Fintype γ] (μ : γ → Measure α) (ν : γ → Measure β) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow α β γ)
      (.pi fun i ↦ (μ i).prod (ν i))
        ((Measure.pi fun i ↦ μ i).prod (Measure.pi fun i ↦ ν i)) where
  measurable := (MeasurableEquiv.arrowProdEquivProdArrow α β γ).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      exact (FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      exact (FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply, MeasurableEquiv.arrowProdEquivProdArrow,
        MeasurableEquiv.coe_mk, Equiv.arrowProdEquivProdArrow_preimage]
      simp_rw [pi_pi, prod_prod, pi_pi, Finset.prod_mul_distrib]

theorem MeasureTheory.volume_preserving.arrowProdEquivProdArrow (α β γ : Type*) [MeasureSpace α]
    [MeasureSpace β] [Fintype γ] [SigmaFinite (volume : Measure α)]
    [SigmaFinite (volume : Measure β)] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow α β γ) :=
  MeasurePreserving.arrowProdEquivProdArrow α β γ (fun _ ↦ volume) (fun _ ↦ volume)

theorem MeasurablePreserving.prodAssoc {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (π : Measure γ) [SigmaFinite μ]
    [SigmaFinite ν] [SigmaFinite π] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ)
      ((μ.prod ν).prod π) (μ.prod (ν.prod π)) where
  measurable := MeasurableEquiv.prodAssoc.measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_
      (isPiSystem_measurableSet.prod (isPiSystem_measurableSet.prod isPiSystem_measurableSet))
      (μ.toFiniteSpanningSetsIn.prod (ν.toFiniteSpanningSetsIn.prod π.toFiniteSpanningSetsIn))
      ?_).symm
    · refine (generateFrom_eq_prod generateFrom_measurableSet
        (generateFrom_eq_prod ?_ ?_ ?_ ?_) ?_ (IsCountablySpanning.prod ?_ ?_)).symm
      any_goals exact generateFrom_measurableSet
      all_goals exact isCountablySpanning_measurableSet
    · rintro _ ⟨s, _, _, ⟨t, _, ⟨u, _, rfl⟩⟩, rfl⟩
      rw [MeasurableEquiv.map_apply, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk,
        Equiv.prod_assoc_preimage, prod_prod, prod_prod, prod_prod, prod_prod, mul_assoc]

theorem MeasureTheory.volume_preserving.prodAssoc {α β γ : Type*} [MeasureSpace α] [MeasureSpace β]
    [MeasureSpace γ] [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)]
    [SigmaFinite (volume : Measure γ)] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ) :=
  MeasurablePreserving.prodAssoc volume volume volume

def MeasurableEquiv.arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [MeasurableSpace β₁] [MeasurableSpace β₂]
    (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) :
    (α₁ → β₁) ≃ᵐ (α₂ → β₂) where
  __ := Equiv.arrowCongr' hα hβ
  measurable_toFun _ h := by
    exact MeasurableSet.preimage h <|
      measurable_pi_iff.mpr fun _ ↦ hβ.measurable.comp' (measurable_pi_apply _)
  measurable_invFun _ h := by
    exact MeasurableSet.preimage h <|
      measurable_pi_iff.mpr fun _ ↦ hβ.symm.measurable.comp' (measurable_pi_apply _)

theorem MeasurePreserving.arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
    [MeasurableSpace β₁] [MeasurableSpace β₂] (μ : α₁ → Measure β₁) (ν : α₂ → Measure β₂)
    [∀ i, SigmaFinite (ν i)] (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂)
    (hm : ∀ i, MeasurePreserving hβ (μ i) (ν (hα i))) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' hα hβ) (Measure.pi fun i ↦ μ i)
      (Measure.pi fun i ↦ ν i) := by
  classical
  convert (measurePreserving_piCongrLeft (fun i : α₂ ↦ ν i) hα).comp
    (measurePreserving_pi μ (fun i : α₁ ↦ ν (hα i)) hm)
  simp only [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, EquivLike.coe_coe,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.symm_symm_apply, Equiv.piCongrLeft'_symm, Equiv.symm_symm]
  rfl

theorem MeasureTheory.volume_preserving.arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
    [MeasureSpace β₁] [MeasureSpace β₂] [SigmaFinite (volume : Measure β₂)]
    (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) (hm : MeasurePreserving hβ) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' hα hβ) :=
  MeasurePreserving.arrowCongr' (fun _ ↦ volume) (fun _ ↦ volume) hα hβ (fun _ ↦ hm)

def MeasurableEquiv.subtypeEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {p : α → Prop} {q : β → Prop} (e : α ≃ᵐ β) (h : ∀ x, p x ↔ q (e x)) :
    {a : α // p a} ≃ᵐ {b : β // q b} where
  __ := Equiv.subtypeEquiv e h
  measurable_toFun _ h := by
    exact MeasurableSet.preimage h (e.measurable.comp' measurable_subtype_coe).subtype_mk
  measurable_invFun _ h := by
    exact MeasurableSet.preimage h (e.symm.measurable.comp' measurable_subtype_coe).subtype_mk

theorem MeasurablePreserving.subtypeEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) {p : α → Prop} {q : β → Prop} (hq : MeasurableSet {x | q x})
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (h : ∀ x, p x ↔ q (e x)) :
    MeasurePreserving (MeasurableEquiv.subtypeEquiv e h)
      (μ.comap Subtype.val) (ν.comap Subtype.val) where
  measurable := (e.subtypeEquiv h).measurable
  map_eq := by
    have heq : MeasurableEmbedding Subtype.val := MeasurableEmbedding.subtype_coe hq
    ext _ hs
    erw [MeasurableEmbedding.map_apply (e.subtypeEquiv h).measurableEmbedding,
      MeasurableEmbedding.comap_apply heq, MeasurableEmbedding.comap_apply, ← he.measure_preimage]
    · congr; aesop
    · exact (heq.measurableSet_image.mpr hs).nullMeasurableSet
    · convert (e.symm.measurableEmbedding.comp heq).comp (e.subtypeEquiv h).measurableEmbedding
      ext
      simp only [Set.mem_setOf_eq, MeasurableEquiv.subtypeEquiv, MeasurableEquiv.coe_mk,
        Function.comp_apply, Equiv.subtypeEquiv_apply, EquivLike.coe_coe,
        MeasurableEquiv.symm_apply_apply]

def MeasurableEquiv.subtypeEquivRight {α : Type*} [MeasurableSpace α] {p : α → Prop} {q : α → Prop}
    (e : ∀ x, p x ↔ q x) :
    { x : α // p x } ≃ᵐ { x : α // q x } := subtypeEquiv (MeasurableEquiv.refl _) e

theorem MeasurablePreserving.subtypeEquivRight {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p : α → Prop} {q : α → Prop} (hq : MeasurableSet {x | q x}) (e : ∀ x, p x ↔ q x) :
    MeasurePreserving (MeasurableEquiv.subtypeEquivRight e) (μ.comap Subtype.val)
      (μ.comap Subtype.val) :=
  MeasurablePreserving.subtypeEquiv μ μ hq (MeasurableEquiv.refl _) (MeasurePreserving.id _) _

end Measure

theorem Complex.dist_induced (x y : ℝ) :
    dist (x : ℂ) (y : ℂ) = dist x y := by
  rw [Complex.dist_of_im_eq (by rfl), Complex.ofReal_re, Complex.ofReal_re]

theorem Complex.ofReal_uniformEmbedding : UniformEmbedding (Complex.ofReal) := by
  simp_rw [Metric.uniformEmbedding_iff', Complex.ofReal_eq_coe, Complex.dist_induced, and_self]
  exact fun ε hε ↦ ⟨ε, hε, fun h ↦ h⟩

section Topo

open Set

theorem closure_lt_eq_le {α β : Type*} [TopologicalSpace α] [PartialOrder α] [OrderClosedTopology α]
    [TopologicalSpace β] {f : β → α}  {g : β → α} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ ⦃x⦄, f x = g x → ∃ᶠ y in nhds x, f y < g y) :
    closure {b | f b < g b} = {b | f b ≤ g b} := by
  refine le_antisymm (closure_lt_subset_le hf hg) fun x hx ↦ ?_
  obtain (hx₁| hx₂) := le_iff_eq_or_lt.mp hx
  · exact mem_closure_iff_frequently.mpr (h hx₁)
  · exact subset_closure hx₂

theorem frontier_le_eq_eq {α β : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {f : β → α} {g : β → α} [TopologicalSpace β] (hf : Continuous f)  (hg : Continuous g)
    (h : ∀ ⦃x⦄, g x = f x → ∃ᶠ y in nhds x, g y < f y) :
    frontier {b | f b ≤ g b} = {b | f b = g b} := by
  rw [frontier_eq_closure_inter_closure, closure_le_eq hf hg]
  ext x
  rw [show {x | f x ≤ g x}ᶜ = {x | g x < f x} by ext; simp, closure_lt_eq_le hg hf h]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, le_antisymm_iff]

theorem frontier_lt_eq_eq {α β : Type*} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {f : β → α} {g : β → α} [TopologicalSpace β] (hf : Continuous f)  (hg : Continuous g)
    (h : ∀ ⦃x⦄, f x = g x → ∃ᶠ y in nhds x, f y < g y) :
    frontier {b | f b < g b} = {b | f b = g b} := by
  simpa only [eq_comm, ← not_lt, ← Set.compl_setOf, frontier_compl] using frontier_le_eq_eq hg hf h

end Topo

theorem Set.indicator_one_eq_indicator_one_iff {ι : Type*} (M₀ : Type*) [MulZeroOneClass M₀]
    {s : Set ι} {t : Set ι} [Nontrivial M₀] :
    s.indicator (1 : ι → M₀) = t.indicator 1 ↔ s = t :=
  ⟨fun h ↦ indicator_one_inj M₀ h, fun h ↦ by rw [h]⟩

open MeasureTheory MeasureTheory.Measure

open Set in
theorem lintegral_comp_abs {f : ℝ → ENNReal} (hf : Measurable f) :
    ∫⁻ x, f |x| = 2 * ∫⁻ x in Ioi 0, f x := by
  calc
    _ = (∫⁻ x in Iic 0, f |x|) + ∫⁻ x in Ioi 0, f |x| := by
      rw [← lintegral_union measurableSet_Ioi (Iic_disjoint_Ioi le_rfl), Iic_union_Ioi,
        setLIntegral_univ]
    _ = (∫⁻ x in Iio 0, f (-x)) + ∫⁻ x in Ioi 0, f x := by
      rw [restrict_Iio_eq_restrict_Iic]
      congr 1
      · refine setLIntegral_congr_fun measurableSet_Iic ?_
        exact Filter.Eventually.of_forall fun x hx ↦ by rw [abs_of_nonpos hx]
      · refine setLIntegral_congr_fun measurableSet_Ioi ?_
        exact Filter.Eventually.of_forall fun x hx ↦ by rw [abs_of_pos (by convert hx)]
    _ = 2 * ∫⁻ x in Ioi 0, f x := by
      rw [two_mul, show Iio (0 : ℝ) = (fun x ↦ -x) ⁻¹' Ioi 0 by simp,
        ← (setLIntegral_map measurableSet_Ioi hf measurable_neg), Measure.map_neg_eq_self]

theorem MeasureTheory.Measure.restrict_prod_eq_univ_prod {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite ν] [MeasureTheory.SFinite μ]  (t : Set β) :
    μ.prod (ν.restrict t) = (μ.prod ν).restrict (Set.univ ×ˢ t) := by
  have : μ = μ.restrict Set.univ := Measure.restrict_univ.symm
  rw [this, Measure.prod_restrict, ← this]

theorem Real.rpow_ne_zero_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y ≠ 0 := by
  rw [rpow_def_of_pos hx]; apply exp_ne_zero _

-- theorem Basis.total_eq_iff_eq_repr {M R ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
--     (B : Basis ι R M) (x : M) (c : ι →₀ R) : Finsupp.total ι M R B c = x ↔ c = B.repr x :=
--   ⟨fun h ↦ by rw [← h, B.repr_total], fun h ↦ by rw [h, B.total_repr]⟩

-- Is it a good idea to use equivFun?
theorem Basis.sum_eq_iff_eq_equivFun {M R ι : Type*} [Fintype ι] [Semiring R] [AddCommMonoid M]
    [Module R M] (B : Basis ι R M) (x : M) (c : ι → R) :
    ∑ i, (c i) • (B i) = x ↔ c = B.equivFun x :=
  ⟨fun h ↦ by rw [← h, B.equivFun_apply, B.repr_sum_self], fun h ↦ by rw [h, B.sum_equivFun]⟩

theorem ContinuousLinearEquiv.image_interior {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type*} [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂)  (s : Set M₁) :
    e '' interior s = interior (e '' s) :=
  e.toHomeomorph.image_interior s

theorem ContinuousLinearEquiv.preimage_interior {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type*} [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] (e : M₁ ≃SL[σ₁₂] M₂) (s : Set M₂) :
    e ⁻¹' interior s = interior (e ⁻¹' s) :=
  e.toHomeomorph.preimage_interior s

def ContinuousLinearEquiv.piCongrRight {R : Type*} [Semiring R] {ι : Type*} {M : ι → Type*}
    [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {N : ι → Type*}
    [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : (i : ι) → M i ≃L[R] N i) :
    ((i : ι) → M i) ≃L[R] (i : ι) → N i :=
  { LinearEquiv.piCongrRight fun i ↦ f i with
    continuous_toFun := by
      exact continuous_pi fun i ↦ (f i).continuous_toFun.comp (continuous_apply i)
    continuous_invFun := by
      exact continuous_pi fun i => (f i).continuous_invFun.comp (continuous_apply i) }

@[simp]
theorem ContinuousLinearEquiv.piCongrRight_apply {R : Type*} [Semiring R] {ι : Type*}
    {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : (i : ι) → M i ≃L[R] N i) (m : (i : ι) → M i) (i : ι) :
    ContinuousLinearEquiv.piCongrRight f m i = (f i) (m i) := rfl

@[simp]
theorem ContinuousLinearEquiv.piCongrRight_symm_apply {R : Type*} [Semiring R] {ι : Type*}
    {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {N : ι → Type*} [∀ i, TopologicalSpace (N i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : (i : ι) → M i ≃L[R] N i) (n : (i : ι) → N i) (i : ι) :
    (ContinuousLinearEquiv.piCongrRight f).symm n i = (f i).symm (n i) := rfl

def ContinuousLinearEquiv.neg (R : Type*) {M : Type*} [Semiring R] [AddCommGroup M]
    [TopologicalSpace M] [ContinuousNeg M] [Module R M] :
    M ≃L[R] M :=
  { LinearEquiv.neg R with
    continuous_toFun := continuous_neg
    continuous_invFun := continuous_neg }

@[simp]
theorem ContinuousLinearEquiv.coe_neg {R : Type*} {M : Type*} [Semiring R] [AddCommGroup M]
    [TopologicalSpace M] [ContinuousNeg M] [Module R M] :
    ⇑(neg R : M ≃L[R] M) = -id := rfl

@[simp]
theorem ContinuousLinearEquiv.neg_apply {R : Type*} {M : Type*} [Semiring R] [AddCommGroup M]
    [TopologicalSpace M] [ContinuousNeg M] [Module R M] (x : M) : neg R x = -x := by simp

@[simp]
theorem ContinuousLinearEquiv.symm_neg {R : Type*} {M : Type*} [Semiring R] [AddCommGroup M]
    [TopologicalSpace M] [ContinuousNeg M] [Module R M] :
    (neg R : M ≃L[R] M).symm = neg R := rfl

@[simp]
theorem ContinuousLinearEquiv.refl_apply (R₁ : Type*) [Semiring R₁] (M₁ : Type*)
    [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁] (x : M₁) :
    ContinuousLinearEquiv.refl R₁ M₁ x = x := rfl
