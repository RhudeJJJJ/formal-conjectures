/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
import Proofs.RadenkovicGutmanD3Long00StagedU
import Proofs.RadenkovicGutmanD3Long00StagedUNode086
import Proofs.RadenkovicGutmanD3Long00StagedUNode107
import Proofs.RadenkovicGutmanD3Long00StagedUNode116
import Proofs.RadenkovicGutmanD3Long00StagedUNode242
import Proofs.RadenkovicGutmanD3Long00StagedUNode277
import Proofs.RadenkovicGutmanD3Long00StagedUNode292
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedNormPack
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open FixedDegree03Long00StagedU
theorem u_expression : e086=NestedClassPolynomials.programU 3 4 4 := by rfl
theorem u_inverse_expression : e242=(NestedReciprocal.homogenize (NestedClassPolynomials.programU 3 4 4)).2 := by rfl
theorem u_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programU 3 4 4)).1=88 := by decide +kernel
noncomputable def u : NestedHorner.Poly 3 := p086
noncomputable def ui : NestedHorner.Poly 3 := p242
theorem v_expression : e107=NestedClassPolynomials.programV 3 4 4 := by rfl
theorem v_inverse_expression : e277=(NestedReciprocal.homogenize (NestedClassPolynomials.programV 3 4 4)).2 := by rfl
theorem v_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programV 3 4 4)).1=84 := by decide +kernel
noncomputable def v : NestedHorner.Poly 3 := p107
noncomputable def vi : NestedHorner.Poly 3 := p277
theorem j_expression : e116=NestedClassPolynomials.programJ 3 4 4 := by rfl
theorem j_inverse_expression : e292=(NestedReciprocal.homogenize (NestedClassPolynomials.programJ 3 4 4)).2 := by rfl
theorem j_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programJ 3 4 4)).1=88 := by decide +kernel
noncomputable def j : NestedHorner.Poly 3 := p116
noncomputable def ji : NestedHorner.Poly 3 := p292
noncomputable def pack : NormProgramPack.Pack 3 4 4 := {
  u := u
  ui := ui
  du := 88
  v := v
  vi := vi
  dv := 84
  j := j
  ji := ji
  dj := 88
  hu := by rw [← u_expression]; exact h086
  hui := by rw [← u_inverse_expression]; exact h242
  hdu := u_degree
  hv := by rw [← v_expression]; exact h107
  hvi := by rw [← v_inverse_expression]; exact h277
  hdv := v_degree
  hj := by rw [← j_expression]; exact h116
  hji := by rw [← j_inverse_expression]; exact h292
  hdj := j_degree
}
#print axioms pack
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedNormPack
