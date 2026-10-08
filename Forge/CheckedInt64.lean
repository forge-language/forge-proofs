/-!
# Signed 64-bit constant-folding boundaries

Executable specification of the safety guards in `compiler/optimize.c`.
This does not make generated native arithmetic safe: emission still requires
a separate overflow policy. Integer division truncates toward zero, as in C.
-/
namespace Forge

def int64Min : Int := -9223372036854775808
def int64Max : Int := 9223372036854775807

def inInt64 (n : Int) : Prop := int64Min ≤ n ∧ n ≤ int64Max
instance (n : Int) : Decidable (inInt64 n) := inferInstanceAs
  (Decidable (int64Min ≤ n ∧ n ≤ int64Max))

def checkedInt64 (n : Int) : Option Int :=
  if inInt64 n then some n else none

def checkedDiv64 (a b : Int) : Option Int :=
  if b = 0 ∨ (a = int64Min ∧ b = -1) then none
  else checkedInt64 (a.tdiv b)

def checkedMod64 (a b : Int) : Option Int :=
  if b = 0 ∨ (a = int64Min ∧ b = -1) then none
  else checkedInt64 (a.tmod b)

theorem checkedInt64_sound (n result : Int)
    (h : checkedInt64 n = some result) : result = n ∧ inInt64 result := by
  unfold checkedInt64 at h
  split at h
  · cases h; exact ⟨rfl, ‹inInt64 n›⟩
  · cases h

theorem checkedDiv64_result_in_range (a b result : Int)
    (h : checkedDiv64 a b = some result) : inInt64 result := by
  unfold checkedDiv64 at h
  split at h
  · cases h
  · exact (checkedInt64_sound _ _ h).2

theorem checkedMod64_result_in_range (a b result : Int)
    (h : checkedMod64 a b = some result) : inInt64 result := by
  unfold checkedMod64 at h
  split at h
  · cases h
  · exact (checkedInt64_sound _ _ h).2

theorem division_by_zero_rejected (a : Int) : checkedDiv64 a 0 = none := by
  simp [checkedDiv64]

theorem remainder_by_zero_rejected (a : Int) : checkedMod64 a 0 = none := by
  simp [checkedMod64]

theorem minimum_division_overflow_rejected : checkedDiv64 int64Min (-1) = none := by
  simp [checkedDiv64]

theorem minimum_remainder_overflow_rejected : checkedMod64 int64Min (-1) = none := by
  simp [checkedMod64]

theorem negative_division_truncates : checkedDiv64 (-7) 3 = some (-2) := by decide
theorem negative_remainder_sign : checkedMod64 (-7) 3 = some (-1) := by decide
theorem addition_overflow_rejected : checkedInt64 (int64Max + 1) = none := by decide
theorem subtraction_overflow_rejected : checkedInt64 (int64Min - 1) = none := by decide

end Forge
