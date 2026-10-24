/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
import Proofs.RadenkovicGutmanStagedExprCompile
import Proofs.RadenkovicGutmanExprDecidableEquality
import Proofs.RadenkovicGutmanD2Long00CompositionalNode086
import Proofs.RadenkovicGutmanD2Long00CompositionalNode107
import Proofs.RadenkovicGutmanD2Long00CompositionalNode116
import Proofs.RadenkovicGutmanD2Long00CompositionalNode242
import Proofs.RadenkovicGutmanD2Long00CompositionalNode277
import Proofs.RadenkovicGutmanD2Long00CompositionalNode292
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00CompositionalNormPack
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open FixedDegree02Long00Compositional
theorem u_expression : e086=NestedClassPolynomials.programU 2 4 4 := by decide +kernel
#print axioms u_expression
theorem u_inverse_expression : e242=(NestedReciprocal.homogenize (NestedClassPolynomials.programU 2 4 4)).2 := by decide +kernel
#print axioms u_inverse_expression
theorem u_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programU 2 4 4)).1=88 := by decide +kernel
#print axioms u_degree
noncomputable def u : NestedHorner.Poly 3 := p086
noncomputable def ui : NestedHorner.Poly 3 := p242
theorem v_expression : e107=NestedClassPolynomials.programV 2 4 4 := by decide +kernel
#print axioms v_expression
theorem v_inverse_expression : e277=(NestedReciprocal.homogenize (NestedClassPolynomials.programV 2 4 4)).2 := by decide +kernel
#print axioms v_inverse_expression
theorem v_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programV 2 4 4)).1=84 := by decide +kernel
#print axioms v_degree
noncomputable def v : NestedHorner.Poly 3 := p107
noncomputable def vi : NestedHorner.Poly 3 := p277
theorem j_expression : e116=NestedClassPolynomials.programJ 2 4 4 := by decide +kernel
#print axioms j_expression
theorem j_inverse_expression : e292=(NestedReciprocal.homogenize (NestedClassPolynomials.programJ 2 4 4)).2 := by decide +kernel
#print axioms j_inverse_expression
theorem j_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programJ 2 4 4)).1=88 := by decide +kernel
#print axioms j_degree
noncomputable def j : NestedHorner.Poly 3 := p116
noncomputable def ji : NestedHorner.Poly 3 := p292
noncomputable def pack : NormProgramPack.Pack 2 4 4 := {
  u := u
  ui := ui
  du := 88
  v := v
  vi := vi
  dv := 84
  j := j
  ji := ji
  dj := 88
  hu := StagedExprCompile.compile_of_identity e086 (NestedClassPolynomials.programU 2 4 4) p086 u_expression h086
  hui := StagedExprCompile.compile_of_identity e242 (NestedReciprocal.homogenize (NestedClassPolynomials.programU 2 4 4)).2 p242 u_inverse_expression h242
  hdu := u_degree
  hv := StagedExprCompile.compile_of_identity e107 (NestedClassPolynomials.programV 2 4 4) p107 v_expression h107
  hvi := StagedExprCompile.compile_of_identity e277 (NestedReciprocal.homogenize (NestedClassPolynomials.programV 2 4 4)).2 p277 v_inverse_expression h277
  hdv := v_degree
  hj := StagedExprCompile.compile_of_identity e116 (NestedClassPolynomials.programJ 2 4 4) p116 j_expression h116
  hji := StagedExprCompile.compile_of_identity e292 (NestedReciprocal.homogenize (NestedClassPolynomials.programJ 2 4 4)).2 p292 j_inverse_expression h292
  hdj := j_degree
}
#print axioms pack
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00CompositionalNormPack
