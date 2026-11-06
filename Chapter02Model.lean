module

public import Chapter02
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Concrete Chapter2 formulation and selected tangent master. All finite rows
are literal sums. The domain-restricted variants record additional domain
conditions; Set.univ recovers the source's global joint-convex formulation.
The bounded epigraph is a separate repair of the compactness qualification. -/

noncomputable section
open scoped BigOperators
namespace Chapter02

abbrev Point (n m : ℕ) := RealVector n × RealVector m

structure ModelData (n m l r : ℕ) where
  g : Fin l → Point n m → ℝ
  A : Fin r → Fin n → ℝ
  B : Fin r → Fin m → ℝ
  rhs : Fin r → ℝ
  c1 : RealVector n
  c2 : RealVector m
  lo : RealVector m
  hi : RealVector m

def LinearForm {n m : ℕ} (a : RealVector n) (b : RealVector m) (p : Point n m) : ℝ :=
  (∑ i, a i * p.1 i) + ∑ i, b i * p.2 i

def ModelData.objective {n m l r : ℕ} (d : ModelData n m l r) := LinearForm d.c1 d.c2

def ModelData.linearRegion {n m l r : ℕ} (d : ModelData n m l r) : Set (Point n m) :=
  {p | ∀ row, LinearForm (d.A row) (d.B row) p ≤ d.rhs row}

def ModelData.nonlinearRegion {n m l r : ℕ} (d : ModelData n m l r) : Set (Point n m) :=
  {p | ∀ j, d.g j p ≤ 0}

def ModelData.feasibleOn {n m l r : ℕ} (d : ModelData n m l r) (S : Set (Point n m)) :=
  MixedFeasible (S ∩ d.nonlinearRegion) d.linearRegion d.lo d.hi

def ModelData.relaxationOn {n m l r : ℕ} (d : ModelData n m l r) (S : Set (Point n m)) :=
  ContinuousRelaxation (S ∩ d.nonlinearRegion) d.linearRegion d.lo d.hi

theorem source_feasible_iff {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (p : Point n m) : p ∈ d.feasibleOn S ↔
      p ∈ S ∧ (∀ j, d.g j p ≤ 0) ∧
      (∀ row, LinearForm (d.A row) (d.B row) p ≤ d.rhs row) ∧
      (∃ y : IntVector m, (∀ i, d.lo i ≤ (y i : ℝ) ∧ (y i : ℝ) ≤ d.hi i) ∧
        p.2 = fun i => (y i : ℝ)) := by
  simp [ModelData.feasibleOn, MixedFeasible, ModelData.nonlinearRegion,
    ModelData.linearRegion, IntegerCylinder, IntegerBox, and_assoc]

theorem linearForm_affine {n m : ℕ} (a : RealVector n) (b : RealVector m)
    (p q : Point n m) (s t : ℝ) :
    LinearForm a b (s • p + t • q) = s * LinearForm a b p + t * LinearForm a b q := by
  simp only [LinearForm, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    ← mul_assoc, mul_comm _ s, mul_comm _ t, Finset.mul_sum]
  ring

theorem linearForm_continuous {n m : ℕ} (a : RealVector n) (b : RealVector m) :
    Continuous (LinearForm a b) := by
  unfold LinearForm
  fun_prop

theorem source_linearRegion_convex {n m l r : ℕ} (d : ModelData n m l r) :
    Convex ℝ d.linearRegion := by
  intro p hp q hq s t hs ht hst row
  rw [linearForm_affine]
  calc
    s * LinearForm (d.A row) (d.B row) p + t * LinearForm (d.A row) (d.B row) q
        ≤ s * d.rhs row + t * d.rhs row := add_le_add
          (mul_le_mul_of_nonneg_left (hp row) hs)
          (mul_le_mul_of_nonneg_left (hq row) ht)
    _ = d.rhs row := by rw [← add_mul, hst, one_mul]

theorem source_nonlinearRegion_convex_on {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (hS : Convex ℝ S) (hg : ∀ j, ConvexOn ℝ S (d.g j)) :
    Convex ℝ (S ∩ d.nonlinearRegion) := by
  intro p hp q hq s t hs ht hst
  exact ⟨hS hp.1 hq.1 hs ht hst, fun j => (hg j).2 hp.1 hq.1 hs ht hst |>.trans
    (by calc
      s * d.g j p + t * d.g j q ≤ s * 0 + t * 0 := add_le_add
        (mul_le_mul_of_nonneg_left (hp.2 j) hs)
        (mul_le_mul_of_nonneg_left (hq.2 j) ht)
      _ = 0 := by ring)⟩

theorem source_relaxation_convex_on {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) (hS : Convex ℝ S) (hg : ∀ j, ConvexOn ℝ S (d.g j)) :
    Convex ℝ (d.relaxationOn S) :=
  continuousRelaxation_convex d.lo d.hi (source_nonlinearRegion_convex_on d S hS hg)
    (source_linearRegion_convex d)

theorem source_mixed_subset_relaxation {n m l r : ℕ} (d : ModelData n m l r)
    (S : Set (Point n m)) : d.feasibleOn S ⊆ d.relaxationOn S :=
  mixed_subset_relaxation _ _ _ _

theorem source_feasible_compact {n m l r : ℕ} (d : ModelData n m l r)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j)) : IsCompact (d.feasibleOn Set.univ) := by
  have hN : IsClosed d.nonlinearRegion := by
    have heq : d.nonlinearRegion = ⋂ j, {p | d.g j p ≤ 0} := by
      ext p
      simp [ModelData.nonlinearRegion]
    rw [heq]
    exact isClosed_iInter fun j => isClosed_le (hg j) continuous_const
  have heq : d.feasibleOn Set.univ =
      d.nonlinearRegion ∩ (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi) := by
    ext p
    simp [ModelData.feasibleOn, MixedFeasible, and_assoc]
  rw [heq]
  exact hbase.inter_left hN

theorem source_minimum_attained {n m l r : ℕ} (d : ModelData n m l r)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j)) (hne : (d.feasibleOn Set.univ).Nonempty) :
    ∃ p, IsMinimizer (d.feasibleOn Set.univ) d.objective p :=
  compact_feasible_attainment (source_feasible_compact d hbase hg) hne
    (linearForm_continuous d.c1 d.c2).continuousOn

/-- k is the finite number of cut origins, not an algorithm execution trace.
Only j in selected i is included, matching source J_i (final paper A_i). -/
structure TangentFamily (n m l k : ℕ) where
  origin : Fin k → Point n m
  selected : Fin k → Set (Fin l)
  derivative : Fin k → Fin l → Point n m →L[ℝ] ℝ

def TangentFamily.cutRegion {n m l r k : ℕ} (c : TangentFamily n m l k)
    (d : ModelData n m l r) : Set (Point n m) :=
  {p | ∀ i j, j ∈ c.selected i →
    d.g j (c.origin i) + c.derivative i j (p - c.origin i) ≤ 0}

def ModelData.masterOn {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k) (S : Set (Point n m)) :=
  MixedFeasible (S ∩ c.cutRegion d) d.linearRegion d.lo d.hi

theorem zero_cuts_universal {n m l r : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l 0) : c.cutRegion d = Set.univ := by
  ext p
  simp [TangentFamily.cutRegion]

theorem selected_cutRegion_convex {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k) : Convex ℝ (c.cutRegion d) := by
  intro p hp q hq s t hs ht hst i j hj
  have hid : s • p + t • q - c.origin i =
      s • (p - c.origin i) + t • (q - c.origin i) := by
    have ho : s • c.origin i + t • c.origin i = c.origin i := by
      rw [← add_smul, hst, one_smul]
    calc
      s • p + t • q - c.origin i =
          s • p + t • q - (s • c.origin i + t • c.origin i) := by rw [ho]
      _ = s • (p - c.origin i) + t • (q - c.origin i) := by
        rw [smul_sub, smul_sub]
        abel
  change d.g j (c.origin i) + c.derivative i j (s • p + t • q - c.origin i) ≤ 0
  rw [hid, map_add, map_smul, map_smul]
  have hsum : d.g j (c.origin i) =
      s * d.g j (c.origin i) + t * d.g j (c.origin i) := by
    rw [← add_mul, hst, one_mul]
  have h1 := mul_le_mul_of_nonneg_left (hp i j hj) hs
  have h2 := mul_le_mul_of_nonneg_left (hq i j hj) ht
  simp only [smul_eq_mul] at *
  nlinarith

theorem selected_cutRegion_closed {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k) : IsClosed (c.cutRegion d) := by
  have heq : c.cutRegion d = ⋂ i, ⋂ j, ⋂ (_ : j ∈ c.selected i),
      {p | d.g j (c.origin i) + c.derivative i j (p - c.origin i) ≤ 0} := by
    ext p
    simp [TangentFamily.cutRegion]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (continuous_const.add ((c.derivative i j).continuous.comp
      (continuous_id.sub continuous_const))) continuous_const

theorem source_master_compact {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi)) :
    IsCompact (d.masterOn c Set.univ) := by
  have heq : d.masterOn c Set.univ =
      c.cutRegion d ∩ (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi) := by
    ext p
    simp [ModelData.masterOn, MixedFeasible, and_assoc]
  rw [heq]
  exact hbase.inter_left (selected_cutRegion_closed d c)

theorem source_master_minimum_attained {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hne : (d.masterOn c Set.univ).Nonempty) :
    ∃ p, IsMinimizer (d.masterOn c Set.univ) d.objective p :=
  compact_feasible_attainment (source_master_compact d c hbase) hne
    (linearForm_continuous d.c1 d.c2).continuousOn

theorem selected_tangents_outer_on {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k) (S : Set (Point n m))
    (hg : ∀ j, ConvexOn ℝ S (d.g j)) (ha : ∀ i, c.origin i ∈ S)
    (hd : ∀ i j, j ∈ c.selected i → HasFDerivAt (d.g j) (c.derivative i j) (c.origin i)) :
    S ∩ d.nonlinearRegion ⊆ S ∩ c.cutRegion d := by
  rintro p ⟨hpS, hp⟩
  exact ⟨hpS, fun i j hj => tangent_cut_valid_on (hg j) (ha i) hpS (hd i j hj) (hp j)⟩

theorem selected_tangents_outer {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k)
    (hg : ∀ j, ConvexOn ℝ Set.univ (d.g j))
    (hd : ∀ i j, j ∈ c.selected i → HasFDerivAt (d.g j) (c.derivative i j) (c.origin i)) :
    d.nonlinearRegion ⊆ c.cutRegion d := by
  intro p hp i j hj
  exact tangent_cut_valid (hg j) (hd i j hj) (hp j)

theorem source_feasible_subset_master {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k) (S : Set (Point n m))
    (hg : ∀ j, ConvexOn ℝ S (d.g j)) (ha : ∀ i, c.origin i ∈ S)
    (hd : ∀ i j, j ∈ c.selected i → HasFDerivAt (d.g j) (c.derivative i j) (c.origin i)) :
    d.feasibleOn S ⊆ d.masterOn c S := by
  rintro p ⟨⟨hpN, hpL⟩, hpY⟩
  exact ⟨⟨selected_tangents_outer_on d c S hg ha hd hpN, hpL⟩, hpY⟩

theorem source_master_lowerBound {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k) (S : Set (Point n m))
    (hg : ∀ j, ConvexOn ℝ S (d.g j)) (ha : ∀ i, c.origin i ∈ S)
    (hd : ∀ i j, j ∈ c.selected i → HasFDerivAt (d.g j) (c.derivative i j) (c.origin i))
    {p : Point n m} (hp : IsMinimizer (d.masterOn c S) d.objective p) :
    IsLowerBound (d.feasibleOn S) d.objective (d.objective p) :=
  lowerBound_of_relaxation (source_feasible_subset_master d c S hg ha hd)
    (minimizer_is_lowerBound hp)

theorem source_master_feasible_minimizer {n m l r k : ℕ} (d : ModelData n m l r)
    (c : TangentFamily n m l k) (S : Set (Point n m))
    (hg : ∀ j, ConvexOn ℝ S (d.g j)) (ha : ∀ i, c.origin i ∈ S)
    (hd : ∀ i j, j ∈ c.selected i → HasFDerivAt (d.g j) (c.derivative i j) (c.origin i))
    {p : Point n m} (hp : IsMinimizer (d.masterOn c S) d.objective p)
    (hfeas : p ∈ d.feasibleOn S) : IsMinimizer (d.feasibleOn S) d.objective p :=
  minimizer_of_relaxation_feasible (source_feasible_subset_master d c S hg ha hd) hp hfeas

/-- Unlike the unbounded-height lift, this set has two explicit real height bounds. -/
def BoundedEpigraph {E : Type*} (S : Set E) (f : E → ℝ) (lo hi : ℝ) : Set (E × ℝ) :=
  {p | p.1 ∈ S ∧ f p.1 ≤ p.2 ∧ lo ≤ p.2 ∧ p.2 ≤ hi}

theorem nonempty_epigraph_not_compact {E : Type*} [TopologicalSpace E]
    {S : Set E} {f : E → ℝ} (hne : S.Nonempty) : ¬ IsCompact (EpigraphLift S f) := by
  intro hc
  obtain ⟨x, hx⟩ := hne
  obtain ⟨u, hu⟩ := (hc.image continuous_snd).bddAbove
  have hmem : (x, max (f x) (u + 1)) ∈ EpigraphLift S f := ⟨hx, le_max_left _ _⟩
  have hbound : max (f x) (u + 1) ≤ u := hu ⟨_, hmem, rfl⟩
  have := le_max_right (f x) (u + 1)
  linarith

theorem compact_objective_bounds {E : Type*} [TopologicalSpace E]
    {S : Set E} {f : E → ℝ} (hS : IsCompact S) (hne : S.Nonempty)
    (hf : ContinuousOn f S) : ∃ lo hi : ℝ, ∀ x ∈ S, lo ≤ f x ∧ f x ≤ hi := by
  obtain ⟨a, ha, hmin⟩ := hS.exists_isMinOn hne hf
  obtain ⟨b, hb, hmax⟩ := hS.exists_isMaxOn hne hf
  exact ⟨f a, f b, fun x hx => ⟨hmin hx, hmax hx⟩⟩

theorem bounded_epigraph_compact {E : Type*} [TopologicalSpace E] [T2Space E]
    {S : Set E} {f : E → ℝ} (hS : IsCompact S) (hf : ContinuousOn f S)
    (lo hi : ℝ) : IsCompact (BoundedEpigraph S f lo hi) := by
  have hc : IsClosed (EpigraphLift S f) := hS.isClosed.epigraph hf
  have heq : BoundedEpigraph S f lo hi = EpigraphLift S f ∩ (Set.univ ×ˢ Set.Icc lo hi) := by
    ext p
    simp [BoundedEpigraph, EpigraphLift, and_assoc]
  rw [heq]
  have hsub : EpigraphLift S f ∩ (Set.univ ×ˢ Set.Icc lo hi) ⊆ S ×ˢ Set.Icc lo hi := by
    intro p hp
    exact ⟨hp.1.1, hp.2.2⟩
  exact (hS.prod isCompact_Icc).of_isClosed_subset
    (hc.inter (isClosed_univ.prod isClosed_Icc)) hsub

theorem bounded_epigraph_minimizer_iff {E : Type*} {S : Set E} {f : E → ℝ}
    {lo hi : ℝ} (hb : ∀ x ∈ S, lo ≤ f x ∧ f x ≤ hi) (p : E × ℝ) :
    IsMinimizer (BoundedEpigraph S f lo hi) Prod.snd p ↔
      IsMinimizer S f p.1 ∧ p.2 = f p.1 := by
  constructor
  · intro hp
    have hgraph : (p.1, f p.1) ∈ BoundedEpigraph S f lo hi :=
      ⟨hp.1.1, le_rfl, hb p.1 hp.1.1⟩
    have htight : p.2 = f p.1 := le_antisymm (hp.2 _ hgraph) hp.1.2.1
    refine ⟨⟨hp.1.1, ?_⟩, htight⟩
    intro x hx
    have hxgraph : (x, f x) ∈ BoundedEpigraph S f lo hi := ⟨hx, le_rfl, hb x hx⟩
    simpa [htight] using hp.2 _ hxgraph
  · rintro ⟨hmin, htight⟩
    refine ⟨?_, ?_⟩
    · exact ⟨hmin.1, by rw [htight], by simpa [htight] using hb p.1 hmin.1⟩
    · intro q hq
      calc
        p.2 = f p.1 := htight
        _ ≤ f q.1 := hmin.2 q.1 hq.1
        _ ≤ q.2 := hq.2.1

theorem compact_bounded_epigraph_exists {E : Type*} [TopologicalSpace E] [T2Space E]
    {S : Set E} {f : E → ℝ} (hS : IsCompact S) (hne : S.Nonempty)
    (hf : ContinuousOn f S) : ∃ lo hi : ℝ,
      IsCompact (BoundedEpigraph S f lo hi) ∧
      (BoundedEpigraph S f lo hi).Nonempty ∧
      (∀ p, IsMinimizer (BoundedEpigraph S f lo hi) Prod.snd p ↔
        IsMinimizer S f p.1 ∧ p.2 = f p.1) := by
  obtain ⟨lo, hi, hb⟩ := compact_objective_bounds hS hne hf
  obtain ⟨x, hx⟩ := hne
  exact ⟨lo, hi, bounded_epigraph_compact hS hf lo hi,
    ⟨(x, f x), hx, le_rfl, hb x hx⟩, bounded_epigraph_minimizer_iff hb⟩

/-- Compactness of the source's linear/integer part also survives the auxiliary
box; valid bounds may be selected on the nonempty original feasible set. This
does not assert compactness of the continuous relaxation or numerical masters. -/
theorem source_bounded_epigraph_exists {n m l r : ℕ} (d : ModelData n m l r)
    (hbase : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (hg : ∀ j, Continuous (d.g j)) (hne : (d.feasibleOn Set.univ).Nonempty) :
    ∃ lo hi : ℝ,
      IsCompact ((d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi) ×ˢ Set.Icc lo hi) ∧
      IsCompact (BoundedEpigraph (d.feasibleOn Set.univ) d.objective lo hi) ∧
      (BoundedEpigraph (d.feasibleOn Set.univ) d.objective lo hi).Nonempty ∧
      (∀ p, IsMinimizer (BoundedEpigraph (d.feasibleOn Set.univ) d.objective lo hi)
        Prod.snd p ↔ IsMinimizer (d.feasibleOn Set.univ) d.objective p.1 ∧
          p.2 = d.objective p.1) := by
  obtain ⟨lo, hi, hc, hn, hm⟩ := compact_bounded_epigraph_exists
    (source_feasible_compact d hbase hg) hne (linearForm_continuous d.c1 d.c2).continuousOn
  exact ⟨lo, hi, hbase.prod isCompact_Icc, hc, hn, hm⟩

end Chapter02

#print axioms Chapter02.source_feasible_iff
#print axioms Chapter02.linearForm_affine
#print axioms Chapter02.linearForm_continuous
#print axioms Chapter02.source_linearRegion_convex
#print axioms Chapter02.source_nonlinearRegion_convex_on
#print axioms Chapter02.source_relaxation_convex_on
#print axioms Chapter02.source_mixed_subset_relaxation
#print axioms Chapter02.source_feasible_compact
#print axioms Chapter02.source_minimum_attained
#print axioms Chapter02.zero_cuts_universal
#print axioms Chapter02.selected_cutRegion_convex
#print axioms Chapter02.selected_cutRegion_closed
#print axioms Chapter02.source_master_compact
#print axioms Chapter02.source_master_minimum_attained
#print axioms Chapter02.selected_tangents_outer_on
#print axioms Chapter02.selected_tangents_outer
#print axioms Chapter02.source_feasible_subset_master
#print axioms Chapter02.source_master_lowerBound
#print axioms Chapter02.source_master_feasible_minimizer
#print axioms Chapter02.nonempty_epigraph_not_compact
#print axioms Chapter02.compact_objective_bounds
#print axioms Chapter02.bounded_epigraph_compact
#print axioms Chapter02.bounded_epigraph_minimizer_iff
#print axioms Chapter02.compact_bounded_epigraph_exists
#print axioms Chapter02.source_bounded_epigraph_exists
