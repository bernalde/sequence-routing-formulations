module

public import Chapter10RoutePadding

@[expose] public section

/-! Adjacent allowed-edge list adapter; frozen F1 definitions are unchanged. -/
noncomputable section
namespace Chapter10.Routing
variable {n : ℕ}

def AllowedWalk (D : Data n) : List (Node n) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => D.allowed a b = true ∧ AllowedWalk D (b :: rest)

theorem allowedWalk_depot_padding (D : Data n) (prev : Node n) (k : ℕ) :
    AllowedWalk D (prev :: List.replicate (k+1) none) ↔
      D.allowed prev none = true ∧ (k = 0 ∨ D.allowed none none = true) := by
  induction k generalizing prev with
  | zero => simp [List.replicate_succ, AllowedWalk]
  | succ k ih =>
    change (D.allowed prev none = true ∧ AllowedWalk D (none :: List.replicate (k+1) none)) ↔ _
    rw [ih]
    simp <;> tauto

theorem padded_allowed_iff (D : Data n) (prev : Node n) (js : List (Fin n)) (k : ℕ) :
    AllowedWalk D (paddedWalk prev js k) ↔
      AllowedFrom D prev js ∧ (k = 0 ∨ D.allowed none none = true) := by
  induction js generalizing prev with
  | nil => exact allowedWalk_depot_padding D prev k
  | cons j js ih =>
    change (D.allowed prev (some j) = true ∧ AllowedWalk D (paddedWalk (some j) js k)) ↔ _
    rw [ih]
    simp only [AllowedFrom, and_assoc]

theorem padded_allowed_forward {D : Data n} {prev js k}
    (h : AllowedWalk D (paddedWalk prev js k)) : AllowedFrom D prev js :=
  ((padded_allowed_iff D prev js k).mp h).1

theorem padded_allowed_reverse {D : Data n} {prev js k}
    (h : AllowedFrom D prev js) (hdd : D.allowed none none = true) :
    AllowedWalk D (paddedWalk prev js k) :=
  (padded_allowed_iff D prev js k).mpr ⟨h,Or.inr hdd⟩

end Chapter10.Routing
