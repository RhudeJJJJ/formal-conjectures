/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReserveIdentity
import Proofs.RadenkovicGutmanNestedIntegerStep
import Proofs.RadenkovicGutmanEscapeReserveSlice00
import Proofs.RadenkovicGutmanEscapeReserveSlice01
import Proofs.RadenkovicGutmanEscapeReserveSlice02
import Proofs.RadenkovicGutmanEscapeReserveSlice03
import Proofs.RadenkovicGutmanEscapeReserveSlice04
import Proofs.RadenkovicGutmanEscapeReserveSlice05
import Proofs.RadenkovicGutmanEscapeReserveSlice06
import Proofs.RadenkovicGutmanEscapeReserveSlice07
import Proofs.RadenkovicGutmanEscapeReserveSlice08
import Proofs.RadenkovicGutmanEscapeReserveSlice09
import Proofs.RadenkovicGutmanEscapeReserveSlice10
import Proofs.RadenkovicGutmanEscapeReserveSlice11
import Proofs.RadenkovicGutmanEscapeReserveSlice12
import Proofs.RadenkovicGutmanEscapeReserveSlice13
import Proofs.RadenkovicGutmanEscapeReserveSlice14
import Proofs.RadenkovicGutmanEscapeReserveSlice15
import Proofs.RadenkovicGutmanEscapeReserveSlice16
import Proofs.RadenkovicGutmanEscapeReserveSlice17
import Proofs.RadenkovicGutmanEscapeReserveSlice18
import Proofs.RadenkovicGutmanEscapeReserveSlice19
import Proofs.RadenkovicGutmanEscapeReserveSlice20
import Proofs.RadenkovicGutmanEscapeReserveSlice21
import Proofs.RadenkovicGutmanEscapeReserveSlice22
import Proofs.RadenkovicGutmanEscapeReserveSlice23
import Proofs.RadenkovicGutmanEscapeReserveSlice24
import Proofs.RadenkovicGutmanEscapeReserveSlice25
import Proofs.RadenkovicGutmanEscapeReserveSlice26
import Proofs.RadenkovicGutmanEscapeReserveSlice27
import Proofs.RadenkovicGutmanEscapeReserveSlice28
import Proofs.RadenkovicGutmanEscapeReserveSlice29
import Proofs.RadenkovicGutmanEscapeReserveSlice30
import Proofs.RadenkovicGutmanEscapeReserveSlice31
import Proofs.RadenkovicGutmanEscapeReserveSlice32
import Proofs.RadenkovicGutmanEscapeReserveSlice33
import Proofs.RadenkovicGutmanEscapeReserveSlice34
import Proofs.RadenkovicGutmanEscapeReserveSlice35
import Proofs.RadenkovicGutmanEscapeReserveSlice36
import Proofs.RadenkovicGutmanEscapeReserveSlice37
import Proofs.RadenkovicGutmanEscapeReserveSlice38
import Proofs.RadenkovicGutmanEscapeReserveSlice39
import Proofs.RadenkovicGutmanEscapeReserveSlice40
import Proofs.RadenkovicGutmanEscapeReserveSlice41
import Proofs.RadenkovicGutmanEscapeReserveSlice42
import Proofs.RadenkovicGutmanEscapeReserveSlice43
import Proofs.RadenkovicGutmanEscapeReserveSlice44

/-! Complete first-variable Bernstein coverage; each child polynomial is kernel-checked. -/
namespace Gebendorfer.RadenkovicGutman.EscapeReserveCertificate
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
theorem accepted : NestedIntegerHybrid.accepts 4 degrees data = true := by
  apply NestedIntegerHybrid.bernstein_step
  · change EscapeReserveData.data.length ≤ 45
    exact le_of_eq EscapeReserveData.data_length
  · intro j
    fin_cases j
    · rw [EscapeReserveSlice00.identity]
      exact EscapeReserveSlice00.accepted
    · rw [EscapeReserveSlice01.identity]
      exact EscapeReserveSlice01.accepted
    · rw [EscapeReserveSlice02.identity]
      exact EscapeReserveSlice02.accepted
    · rw [EscapeReserveSlice03.identity]
      exact EscapeReserveSlice03.accepted
    · rw [EscapeReserveSlice04.identity]
      exact EscapeReserveSlice04.accepted
    · rw [EscapeReserveSlice05.identity]
      exact EscapeReserveSlice05.accepted
    · rw [EscapeReserveSlice06.identity]
      exact EscapeReserveSlice06.accepted
    · rw [EscapeReserveSlice07.identity]
      exact EscapeReserveSlice07.accepted
    · rw [EscapeReserveSlice08.identity]
      exact EscapeReserveSlice08.accepted
    · rw [EscapeReserveSlice09.identity]
      exact EscapeReserveSlice09.accepted
    · rw [EscapeReserveSlice10.identity]
      exact EscapeReserveSlice10.accepted
    · rw [EscapeReserveSlice11.identity]
      exact EscapeReserveSlice11.accepted
    · rw [EscapeReserveSlice12.identity]
      exact EscapeReserveSlice12.accepted
    · rw [EscapeReserveSlice13.identity]
      exact EscapeReserveSlice13.accepted
    · rw [EscapeReserveSlice14.identity]
      exact EscapeReserveSlice14.accepted
    · rw [EscapeReserveSlice15.identity]
      exact EscapeReserveSlice15.accepted
    · rw [EscapeReserveSlice16.identity]
      exact EscapeReserveSlice16.accepted
    · rw [EscapeReserveSlice17.identity]
      exact EscapeReserveSlice17.accepted
    · rw [EscapeReserveSlice18.identity]
      exact EscapeReserveSlice18.accepted
    · rw [EscapeReserveSlice19.identity]
      exact EscapeReserveSlice19.accepted
    · rw [EscapeReserveSlice20.identity]
      exact EscapeReserveSlice20.accepted
    · rw [EscapeReserveSlice21.identity]
      exact EscapeReserveSlice21.accepted
    · rw [EscapeReserveSlice22.identity]
      exact EscapeReserveSlice22.accepted
    · rw [EscapeReserveSlice23.identity]
      exact EscapeReserveSlice23.accepted
    · rw [EscapeReserveSlice24.identity]
      exact EscapeReserveSlice24.accepted
    · rw [EscapeReserveSlice25.identity]
      exact EscapeReserveSlice25.accepted
    · rw [EscapeReserveSlice26.identity]
      exact EscapeReserveSlice26.accepted
    · rw [EscapeReserveSlice27.identity]
      exact EscapeReserveSlice27.accepted
    · rw [EscapeReserveSlice28.identity]
      exact EscapeReserveSlice28.accepted
    · rw [EscapeReserveSlice29.identity]
      exact EscapeReserveSlice29.accepted
    · rw [EscapeReserveSlice30.identity]
      exact EscapeReserveSlice30.accepted
    · rw [EscapeReserveSlice31.identity]
      exact EscapeReserveSlice31.accepted
    · rw [EscapeReserveSlice32.identity]
      exact EscapeReserveSlice32.accepted
    · rw [EscapeReserveSlice33.identity]
      exact EscapeReserveSlice33.accepted
    · rw [EscapeReserveSlice34.identity]
      exact EscapeReserveSlice34.accepted
    · rw [EscapeReserveSlice35.identity]
      exact EscapeReserveSlice35.accepted
    · rw [EscapeReserveSlice36.identity]
      exact EscapeReserveSlice36.accepted
    · rw [EscapeReserveSlice37.identity]
      exact EscapeReserveSlice37.accepted
    · rw [EscapeReserveSlice38.identity]
      exact EscapeReserveSlice38.accepted
    · rw [EscapeReserveSlice39.identity]
      exact EscapeReserveSlice39.accepted
    · rw [EscapeReserveSlice40.identity]
      exact EscapeReserveSlice40.accepted
    · rw [EscapeReserveSlice41.identity]
      exact EscapeReserveSlice41.accepted
    · rw [EscapeReserveSlice42.identity]
      exact EscapeReserveSlice42.accepted
    · rw [EscapeReserveSlice43.identity]
      exact EscapeReserveSlice43.accepted
    · rw [EscapeReserveSlice44.identity]
      exact EscapeReserveSlice44.accepted

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
end Gebendorfer.RadenkovicGutman.EscapeReserveCertificate
