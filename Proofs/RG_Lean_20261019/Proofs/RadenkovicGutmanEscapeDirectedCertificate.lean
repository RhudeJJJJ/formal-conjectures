/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeDirectedIdentity
import Proofs.RadenkovicGutmanNestedIntegerStep
import Proofs.RadenkovicGutmanEscapeDirectedSlice00
import Proofs.RadenkovicGutmanEscapeDirectedSlice01
import Proofs.RadenkovicGutmanEscapeDirectedSlice02
import Proofs.RadenkovicGutmanEscapeDirectedSlice03
import Proofs.RadenkovicGutmanEscapeDirectedSlice04
import Proofs.RadenkovicGutmanEscapeDirectedSlice05
import Proofs.RadenkovicGutmanEscapeDirectedSlice06
import Proofs.RadenkovicGutmanEscapeDirectedSlice07
import Proofs.RadenkovicGutmanEscapeDirectedSlice08
import Proofs.RadenkovicGutmanEscapeDirectedSlice09
import Proofs.RadenkovicGutmanEscapeDirectedSlice10
import Proofs.RadenkovicGutmanEscapeDirectedSlice11
import Proofs.RadenkovicGutmanEscapeDirectedSlice12
import Proofs.RadenkovicGutmanEscapeDirectedSlice13
import Proofs.RadenkovicGutmanEscapeDirectedSlice14
import Proofs.RadenkovicGutmanEscapeDirectedSlice15
import Proofs.RadenkovicGutmanEscapeDirectedSlice16
import Proofs.RadenkovicGutmanEscapeDirectedSlice17
import Proofs.RadenkovicGutmanEscapeDirectedSlice18
import Proofs.RadenkovicGutmanEscapeDirectedSlice19
import Proofs.RadenkovicGutmanEscapeDirectedSlice20
import Proofs.RadenkovicGutmanEscapeDirectedSlice21
import Proofs.RadenkovicGutmanEscapeDirectedSlice22

/-! Complete first-variable Bernstein coverage; each child polynomial is kernel-checked. -/
namespace Gebendorfer.RadenkovicGutman.EscapeDirectedCertificate
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
theorem accepted : NestedIntegerHybrid.accepts 4 degrees data = true := by
  apply NestedIntegerHybrid.bernstein_step
  · change EscapeDirectedData.data.length ≤ 23
    exact le_of_eq EscapeDirectedData.data_length
  · intro j
    fin_cases j
    · rw [EscapeDirectedSlice00.identity]
      exact EscapeDirectedSlice00.accepted
    · rw [EscapeDirectedSlice01.identity]
      exact EscapeDirectedSlice01.accepted
    · rw [EscapeDirectedSlice02.identity]
      exact EscapeDirectedSlice02.accepted
    · rw [EscapeDirectedSlice03.identity]
      exact EscapeDirectedSlice03.accepted
    · rw [EscapeDirectedSlice04.identity]
      exact EscapeDirectedSlice04.accepted
    · rw [EscapeDirectedSlice05.identity]
      exact EscapeDirectedSlice05.accepted
    · rw [EscapeDirectedSlice06.identity]
      exact EscapeDirectedSlice06.accepted
    · rw [EscapeDirectedSlice07.identity]
      exact EscapeDirectedSlice07.accepted
    · rw [EscapeDirectedSlice08.identity]
      exact EscapeDirectedSlice08.accepted
    · rw [EscapeDirectedSlice09.identity]
      exact EscapeDirectedSlice09.accepted
    · rw [EscapeDirectedSlice10.identity]
      exact EscapeDirectedSlice10.accepted
    · rw [EscapeDirectedSlice11.identity]
      exact EscapeDirectedSlice11.accepted
    · rw [EscapeDirectedSlice12.identity]
      exact EscapeDirectedSlice12.accepted
    · rw [EscapeDirectedSlice13.identity]
      exact EscapeDirectedSlice13.accepted
    · rw [EscapeDirectedSlice14.identity]
      exact EscapeDirectedSlice14.accepted
    · rw [EscapeDirectedSlice15.identity]
      exact EscapeDirectedSlice15.accepted
    · rw [EscapeDirectedSlice16.identity]
      exact EscapeDirectedSlice16.accepted
    · rw [EscapeDirectedSlice17.identity]
      exact EscapeDirectedSlice17.accepted
    · rw [EscapeDirectedSlice18.identity]
      exact EscapeDirectedSlice18.accepted
    · rw [EscapeDirectedSlice19.identity]
      exact EscapeDirectedSlice19.accepted
    · rw [EscapeDirectedSlice20.identity]
      exact EscapeDirectedSlice20.accepted
    · rw [EscapeDirectedSlice21.identity]
      exact EscapeDirectedSlice21.accepted
    · rw [EscapeDirectedSlice22.identity]
      exact EscapeDirectedSlice22.accepted

#print axioms accepted
theorem form_nonneg (h x a b : ℝ) (hh : h ∈ Ioc (0 : ℝ) (1/46))
    (hx : x ∈ Icc (653/2000 : ℝ) 10) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    0 ≤ form h x a b := by
  let U := (x-(653/2000 : ℝ))/(19347/2000 : ℝ)
  have hU : U ∈ Icc (0 : ℝ) 1 := by dsimp [U]; constructor <;> norm_num at * <;> linarith
  have he : (653/2000 : ℝ)+(19347/2000 : ℝ)*U=x := by dsimp [U]; ring
  have hv : ∀ i : Fin 4, (![46*h,U,a,b] : Fin 4 → ℝ) i ∈ Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · change 46*h ∈ Icc (0 : ℝ) 1
      constructor <;> linarith [hh.1,hh.2]
    · exact hU
    · exact ha
    · exact hb
  have h0 := NestedIntegerHybrid.accepts_sound 4 degrees data accepted _ hv
  have hH : 46*h ≠ 0 := mul_ne_zero (by norm_num) hh.1.ne'
  have hX : (653/2000 : ℝ)+(19347/2000 : ℝ)*U ≠ 0 := by rw [he]; linarith only [hx.1]
  rw [data_identity _ _ _ _ hH hX,he,show 46*h/46=h by ring] at h0
  exact nonneg_of_mul_nonneg_right h0 (by norm_num)

#print axioms form_nonneg
end
end Gebendorfer.RadenkovicGutman.EscapeDirectedCertificate
