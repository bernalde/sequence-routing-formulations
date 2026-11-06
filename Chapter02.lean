module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! Reusable Chapter2 foundations. Source-to-type mappings and additional
hypotheses are recorded separately. There is no solver oracle, KKT axiom,
attainment assumption hidden in an infimum, or whole-algorithm certificate. -/

noncomputable section
namespace Chapter02

abbrev RealVector (n : ℕ) := Fin n → ℝ
abbrev IntVector (m : ℕ) := Fin m → ℤ

def IntegerBox {m : ℕ} (lo hi : RealVector m) : Set (IntVector m) :=
  {y | ∀ i, lo i ≤ (y i : ℝ) ∧ (y i : ℝ) ≤ hi i}

def IntegerCylinder {n m : ℕ} (lo hi : RealVector m) :
    Set (RealVector n × RealVector m) :=
  {p | ∃ y ∈ IntegerBox lo hi, p.2 = fun i => (y i : ℝ)}

def MixedFeasible {n m : ℕ} (N L : Set (RealVector n × RealVector m))
    (lo hi : RealVector m) := N ∩ L ∩ IntegerCylinder (n := n) lo hi

def ContinuousRelaxation {n m : ℕ} (N L : Set (RealVector n × RealVector m))
    (lo hi : RealVector m) : Set (RealVector n × RealVector m) :=
  {p | p ∈ N ∧ p ∈ L ∧ ∀ i, lo i ≤ p.2 i ∧ p.2 i ≤ hi i}

theorem mixed_subset_relaxation {n m : ℕ} (N L : Set (RealVector n × RealVector m))
    (lo hi : RealVector m) : MixedFeasible N L lo hi ⊆ ContinuousRelaxation N L lo hi := by
  rintro p ⟨⟨hN, hL⟩, y, hy, hp⟩
  exact ⟨hN, hL, by simpa [IntegerBox, hp] using hy⟩

theorem integerBox_finite {m : ℕ} (lo hi : RealVector m) : (IntegerBox lo hi).Finite := by
  have heq : IntegerBox lo hi = Set.Icc (fun i => ⌈lo i⌉) (fun i => ⌊hi i⌋) := by
    ext y
    simp [IntegerBox, Set.mem_Icc, Pi.le_def, Int.ceil_le, Int.le_floor, forall_and]
  rw [heq]
  exact Set.finite_Icc _ _

theorem integerBox_nonempty {m : ℕ} (lo hi : RealVector m)
    (h : ∀ i, (⌈lo i⌉ : ℝ) ≤ hi i) : (IntegerBox lo hi).Nonempty := by
  refine ⟨fun i => ⌈lo i⌉, ?_⟩
  intro i
  exact ⟨Int.le_ceil _, h i⟩

theorem continuousRelaxation_convex {n m : ℕ}
    {N L : Set (RealVector n × RealVector m)} (lo hi : RealVector m)
    (hN : Convex ℝ N) (hL : Convex ℝ L) : Convex ℝ (ContinuousRelaxation N L lo hi) := by
  intro p hp q hq a b ha hb hab
  refine ⟨hN hp.1 hq.1 ha hb hab, hL hp.2.1 hq.2.1 ha hb hab, ?_⟩
  intro i
  change lo i ≤ a * p.2 i + b * q.2 i ∧ a * p.2 i + b * q.2 i ≤ hi i
  constructor
  · calc
      lo i = a * lo i + b * lo i := by rw [← add_mul, hab, one_mul]
      _ ≤ a * p.2 i + b * q.2 i := add_le_add
        (mul_le_mul_of_nonneg_left (hp.2.2 i).1 ha)
        (mul_le_mul_of_nonneg_left (hq.2.2 i).1 hb)
  · calc
      a * p.2 i + b * q.2 i ≤ a * hi i + b * hi i := add_le_add
        (mul_le_mul_of_nonneg_left (hp.2.2 i).2 ha)
        (mul_le_mul_of_nonneg_left (hq.2.2 i).2 hb)
      _ = hi i := by rw [← add_mul, hab, one_mul]

def IsMinimizer {A : Type*} (S : Set A) (f : A → ℝ) (x : A) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, f x ≤ f y

def IsLowerBound {A : Type*} (S : Set A) (f : A → ℝ) (v : ℝ) : Prop :=
  ∀ x ∈ S, v ≤ f x

def HasUpperBoundWitness {A : Type*} (S : Set A) (f : A → ℝ) (v : ℝ) : Prop :=
  ∃ x ∈ S, f x ≤ v

theorem compact_feasible_attainment {A : Type*} [TopologicalSpace A]
    {S : Set A} {f : A → ℝ} (hS : IsCompact S) (hne : S.Nonempty)
    (hf : ContinuousOn f S) : ∃ x, IsMinimizer S f x := by
  obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn hne hf
  exact ⟨x, hx, hmin⟩

theorem lowerBound_of_relaxation {A : Type*} {S R : Set A} {f : A → ℝ} {v : ℝ}
    (hSR : S ⊆ R) (hv : IsLowerBound R f v) : IsLowerBound S f v :=
  fun x hx => hv x (hSR hx)

theorem minimizer_is_lowerBound {A : Type*} {R : Set A} {f : A → ℝ} {x : A}
    (hx : IsMinimizer R f x) : IsLowerBound R f (f x) := hx.2

theorem minimizer_of_relaxation_feasible {A : Type*} {S R : Set A} {f : A → ℝ} {x : A}
    (hSR : S ⊆ R) (hx : IsMinimizer R f x) (hfeas : x ∈ S) : IsMinimizer S f x :=
  ⟨hfeas, fun y hy => hx.2 y (hSR hy)⟩

theorem lower_le_upper_witness {A : Type*} {S : Set A} {f : A → ℝ} {l u : ℝ}
    (hl : IsLowerBound S f l) (hu : HasUpperBoundWitness S f u) : l ≤ u := by
  obtain ⟨x, hx, hfu⟩ := hu
  exact (hl x hx).trans hfu

theorem nested_minima_monotone {A : Type*} {R S : Set A} {f : A → ℝ} {x y : A}
    (hSR : S ⊆ R) (hx : IsMinimizer R f x) (hy : IsMinimizer S f y) : f x ≤ f y :=
  hx.2 y (hSR hy.1)

def EpigraphLift {A : Type*} (S : Set A) (f : A → ℝ) : Set (A × ℝ) :=
  {p | p.1 ∈ S ∧ f p.1 ≤ p.2}

theorem epigraph_lift_minimizer {A : Type*} {S : Set A} {f : A → ℝ} {x : A}
    (hx : IsMinimizer S f x) : IsMinimizer (EpigraphLift S f) Prod.snd (x, f x) := by
  refine ⟨⟨hx.1, le_rfl⟩, ?_⟩
  intro p hp
  exact (hx.2 p.1 hp.1).trans hp.2

theorem epigraph_tight_at_minimizer {A : Type*} {S : Set A} {f : A → ℝ} {p : A × ℝ}
    (hp : IsMinimizer (EpigraphLift S f) Prod.snd p) : p.2 = f p.1 := by
  exact le_antisymm (hp.2 (p.1, f p.1) ⟨hp.1.1, le_rfl⟩) hp.1.2

theorem epigraph_project_minimizer {A : Type*} {S : Set A} {f : A → ℝ} {p : A × ℝ}
    (hp : IsMinimizer (EpigraphLift S f) Prod.snd p) : IsMinimizer S f p.1 := by
  refine ⟨hp.1.1, ?_⟩
  intro x hx
  calc
    f p.1 ≤ p.2 := hp.1.2
    _ ≤ f x := hp.2 (x, f x) ⟨hx, le_rfl⟩

theorem epigraph_feasible_iff {A : Type*} (S : Set A) (f : A → ℝ) :
    (EpigraphLift S f).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨p, hp⟩; exact ⟨p.1, hp.1⟩
  · rintro ⟨x, hx⟩; exact ⟨(x, f x), hx, le_rfl⟩

theorem epigraph_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {f : E → ℝ} (hf : ConvexOn ℝ S f) : Convex ℝ (EpigraphLift S f) :=
  hf.convex_epigraph

theorem convex_constraint_sublevel {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {g : E → ℝ} (hg : ConvexOn ℝ S g) :
    Convex ℝ {x ∈ S | g x ≤ 0} := hg.convex_le 0

/-- Analytic first-order underestimation in any real normed vector space.
Convexity on the declared domain is explicit; source gradient/dot-product
notation is represented by the actual Fréchet derivative's linear action. -/
theorem tangent_underestimator_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {D : E →L[ℝ] ℝ} {S : Set E} {a b : E}
    (hconv : ConvexOn ℝ S f) (ha : a ∈ S) (hb : b ∈ S)
    (hderiv : HasFDerivAt f D a) :
    f a + D (b-a) ≤ f b := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a b
  have hc : ConvexOn ℝ (line ⁻¹' S) (f ∘ line) := hconv.comp_affineMap line
  have hd : HasDerivAt (f ∘ line) (D (b-a)) 0 :=
    hderiv.comp_hasDerivAt_of_eq 0 AffineMap.hasDerivAt_lineMap (by simp [line])
  have h0 : (0:ℝ) ∈ line ⁻¹' S := by simpa [line] using ha
  have h1 : (1:ℝ) ∈ line ⁻¹' S := by simpa [line] using hb
  have h := hc.le_slope_of_hasDerivAt h0 h1 (by norm_num) hd
  simp only [line, slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, sub_zero, div_one] at h
  linarith

theorem tangent_underestimator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {D : E →L[ℝ] ℝ} {a b : E}
    (hconv : ConvexOn ℝ Set.univ f) (hderiv : HasFDerivAt f D a) :
    f a + D (b-a) ≤ f b :=
  tangent_underestimator_on hconv (Set.mem_univ _) (Set.mem_univ _) hderiv

theorem tangent_cut_valid_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {D : E →L[ℝ] ℝ} {S : Set E} {a x : E}
    (hconv : ConvexOn ℝ S g) (ha : a ∈ S) (hxS : x ∈ S)
    (hderiv : HasFDerivAt g D a) (hx : g x ≤ 0) :
    g a + D (x-a) ≤ 0 := (tangent_underestimator_on hconv ha hxS hderiv).trans hx

theorem tangent_cut_valid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {D : E →L[ℝ] ℝ} {a x : E}
    (hconv : ConvexOn ℝ Set.univ g) (hderiv : HasFDerivAt g D a) (hx : g x ≤ 0) :
    g a + D (x-a) ≤ 0 := (tangent_underestimator hconv hderiv).trans hx

theorem cut_family_outer {A I J : Type*} (g : J → A → ℝ) (c : I → J → A → ℝ)
    (hc : ∀ i j x, c i j x ≤ g j x) :
    {x | ∀ j, g j x ≤ 0} ⊆ {x | ∀ i j, c i j x ≤ 0} :=
  fun x hx i j => (hc i j x).trans (hx j)

theorem cut_family_outer_on {A I J : Type*} (S : Set A)
    (g : J → A → ℝ) (c : I → J → A → ℝ)
    (hc : ∀ i j x, x ∈ S → c i j x ≤ g j x) :
    {x ∈ S | ∀ j, g j x ≤ 0} ⊆ {x ∈ S | ∀ i j, c i j x ≤ 0} :=
  fun x hx => ⟨hx.1, fun i j => (hc i j x hx.1).trans (hx.2 j)⟩

/-- Exact arithmetic subclaim for the displayed GBD cut's missing anchor.
Original convex MINLP: min x, 0≤x≤2, binary y, x≥y, with inactive
constraint g=x²-4≤0. At the NLP(1) point
xk=yk=1 and multiplier μ=1, the printed objective cut is 1+y≤η.
The correct anchored cut is y≤η. Analytic/KKT/source premises are separate. -/
theorem gbd_printed_cut_excludes_optimum : ¬ ((1:ℝ) + 0 ≤ 0) := by norm_num

theorem gbd_anchored_cut_valid (x y : ℝ) (hxy : y ≤ x) : (1:ℝ) + (y-1) ≤ x := by
  linarith

theorem gbd_printed_feasibility_cut_excludes_point : ¬ ((1/2:ℝ) + 2*0 ≤ 0) := by
  norm_num

theorem gbd_anchored_feasibility_cut_retains_point :
    (1/2:ℝ) + 2*(0-1) ≤ 0 ∧ ¬ ((1/2:ℝ) + 2*(1-1) ≤ 0) := by norm_num

def RelativeRelaxationGapPercent (zstar zrelax : ℝ) : ℝ :=
  |zstar-zrelax| / max |zstar| (1/1000) * 100

theorem relativeGap_denominator_positive (zstar : ℝ) : 0 < max |zstar| (1/1000:ℝ) :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

/-- The benchmark's fixed denominator floor prevents universal scale invariance.
This does not establish any misclassified original benchmark instance. -/
theorem relativeGap_scaling_counterexample :
    RelativeRelaxationGapPercent (1/10000) 0 = 10 ∧
    RelativeRelaxationGapPercent (1/100) 0 = 100 := by
  have hsmall : |(1/10000:ℝ)| = 1/10000 := abs_of_pos (by norm_num)
  have hlarge : |(1/100:ℝ)| = 1/100 := abs_of_pos (by norm_num)
  simp only [RelativeRelaxationGapPercent, sub_zero, hsmall, hlarge]
  norm_num [max_def]

end Chapter02

#print axioms Chapter02.mixed_subset_relaxation
#print axioms Chapter02.integerBox_finite
#print axioms Chapter02.integerBox_nonempty
#print axioms Chapter02.continuousRelaxation_convex
#print axioms Chapter02.compact_feasible_attainment
#print axioms Chapter02.lowerBound_of_relaxation
#print axioms Chapter02.minimizer_is_lowerBound
#print axioms Chapter02.minimizer_of_relaxation_feasible
#print axioms Chapter02.lower_le_upper_witness
#print axioms Chapter02.nested_minima_monotone
#print axioms Chapter02.epigraph_lift_minimizer
#print axioms Chapter02.epigraph_tight_at_minimizer
#print axioms Chapter02.epigraph_project_minimizer
#print axioms Chapter02.epigraph_feasible_iff
#print axioms Chapter02.epigraph_convex
#print axioms Chapter02.convex_constraint_sublevel
#print axioms Chapter02.tangent_underestimator_on
#print axioms Chapter02.tangent_underestimator
#print axioms Chapter02.tangent_cut_valid_on
#print axioms Chapter02.tangent_cut_valid
#print axioms Chapter02.cut_family_outer
#print axioms Chapter02.cut_family_outer_on
#print axioms Chapter02.gbd_printed_cut_excludes_optimum
#print axioms Chapter02.gbd_anchored_cut_valid
#print axioms Chapter02.gbd_printed_feasibility_cut_excludes_point
#print axioms Chapter02.gbd_anchored_feasibility_cut_retains_point
#print axioms Chapter02.relativeGap_denominator_positive
#print axioms Chapter02.relativeGap_scaling_counterexample
