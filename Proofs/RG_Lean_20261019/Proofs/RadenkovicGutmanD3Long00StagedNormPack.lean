/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
import Proofs.RadenkovicGutmanD3Long00StagedU
import Proofs.RadenkovicGutmanD3Long00StagedUNode086
import Proofs.RadenkovicGutmanD3Long00StagedUNode107
import Proofs.RadenkovicGutmanD3Long00StagedUNode116
import Proofs.RadenkovicGutmanD3Long00StagedUNode242
import Proofs.RadenkovicGutmanD3Long00StagedUNode277
import Proofs.RadenkovicGutmanD3Long00StagedUNode292
import Proofs.RadenkovicGutmanStagedExprCompile
import Proofs.RadenkovicGutmanExprDecidableEquality
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedNormPack
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open FixedDegree03Long00StagedU
theorem u_expression : e086=NestedClassPolynomials.programU 3 4 4 := by decide +kernel
theorem u_inverse_expression : e242=(NestedReciprocal.homogenize (NestedClassPolynomials.programU 3 4 4)).2 := by decide +kernel
theorem u_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programU 3 4 4)).1=88 := by decide +kernel
noncomputable def u : NestedHorner.Poly 3 := p086
noncomputable def ui : NestedHorner.Poly 3 := p242
theorem v_expression : e107=NestedClassPolynomials.programV 3 4 4 := by decide +kernel
theorem v_inverse_expression : e277=(NestedReciprocal.homogenize (NestedClassPolynomials.programV 3 4 4)).2 := by decide +kernel
theorem v_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programV 3 4 4)).1=84 := by decide +kernel
noncomputable def v : NestedHorner.Poly 3 := p107
noncomputable def vi : NestedHorner.Poly 3 := p277
theorem j_expression : e116=NestedClassPolynomials.programJ 3 4 4 := by decide +kernel
theorem j_inverse_expression : e292=(NestedReciprocal.homogenize (NestedClassPolynomials.programJ 3 4 4)).2 := by decide +kernel
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
  hu := StagedExprCompile.compile_of_identity e086 (NestedClassPolynomials.programU 3 4 4) p086 u_expression h086
  hui := StagedExprCompile.compile_of_identity e242 (NestedReciprocal.homogenize (NestedClassPolynomials.programU 3 4 4)).2 p242 u_inverse_expression h242
  hdu := u_degree
  hv := StagedExprCompile.compile_of_identity e107 (NestedClassPolynomials.programV 3 4 4) p107 v_expression h107
  hvi := StagedExprCompile.compile_of_identity e277 (NestedReciprocal.homogenize (NestedClassPolynomials.programV 3 4 4)).2 p277 v_inverse_expression h277
  hdv := v_degree
  hj := StagedExprCompile.compile_of_identity e116 (NestedClassPolynomials.programJ 3 4 4) p116 j_expression h116
  hji := StagedExprCompile.compile_of_identity e292 (NestedReciprocal.homogenize (NestedClassPolynomials.programJ 3 4 4)).2 p292 j_inverse_expression h292
  hdj := j_degree
}
#print axioms pack
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedNormPack
