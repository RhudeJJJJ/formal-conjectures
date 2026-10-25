/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
import Proofs.RadenkovicGutmanStagedExprCompile
import Proofs.RadenkovicGutmanExprDecidableEquality
import Proofs.RadenkovicGutmanD23Long00CompositionalNode088
import Proofs.RadenkovicGutmanD23Long00CompositionalNode109
import Proofs.RadenkovicGutmanD23Long00CompositionalNode118
import Proofs.RadenkovicGutmanD23Long00CompositionalNode245
import Proofs.RadenkovicGutmanD23Long00CompositionalNode280
import Proofs.RadenkovicGutmanD23Long00CompositionalNode295
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00CompositionalNormPack
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open FixedDegree23Long00Compositional
theorem u_expression : e088=NestedClassPolynomials.programU 23 4 4 := by decide +kernel
#print axioms u_expression
theorem u_inverse_expression : e245=(NestedReciprocal.homogenize (NestedClassPolynomials.programU 23 4 4)).2 := by decide +kernel
#print axioms u_inverse_expression
theorem u_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programU 23 4 4)).1=88 := by decide +kernel
#print axioms u_degree
noncomputable def u : NestedHorner.Poly 3 := p088
noncomputable def ui : NestedHorner.Poly 3 := p245
theorem v_expression : e109=NestedClassPolynomials.programV 23 4 4 := by decide +kernel
#print axioms v_expression
theorem v_inverse_expression : e280=(NestedReciprocal.homogenize (NestedClassPolynomials.programV 23 4 4)).2 := by decide +kernel
#print axioms v_inverse_expression
theorem v_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programV 23 4 4)).1=84 := by decide +kernel
#print axioms v_degree
noncomputable def v : NestedHorner.Poly 3 := p109
noncomputable def vi : NestedHorner.Poly 3 := p280
theorem j_expression : e118=NestedClassPolynomials.programJ 23 4 4 := by decide +kernel
#print axioms j_expression
theorem j_inverse_expression : e295=(NestedReciprocal.homogenize (NestedClassPolynomials.programJ 23 4 4)).2 := by decide +kernel
#print axioms j_inverse_expression
theorem j_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programJ 23 4 4)).1=88 := by decide +kernel
#print axioms j_degree
noncomputable def j : NestedHorner.Poly 3 := p118
noncomputable def ji : NestedHorner.Poly 3 := p295
noncomputable def pack : NormProgramPack.Pack 23 4 4 := {
  u := u
  ui := ui
  du := 88
  v := v
  vi := vi
  dv := 84
  j := j
  ji := ji
  dj := 88
  hu := StagedExprCompile.compile_of_identity e088 (NestedClassPolynomials.programU 23 4 4) p088 u_expression h088
  hui := StagedExprCompile.compile_of_identity e245 (NestedReciprocal.homogenize (NestedClassPolynomials.programU 23 4 4)).2 p245 u_inverse_expression h245
  hdu := u_degree
  hv := StagedExprCompile.compile_of_identity e109 (NestedClassPolynomials.programV 23 4 4) p109 v_expression h109
  hvi := StagedExprCompile.compile_of_identity e280 (NestedReciprocal.homogenize (NestedClassPolynomials.programV 23 4 4)).2 p280 v_inverse_expression h280
  hdv := v_degree
  hj := StagedExprCompile.compile_of_identity e118 (NestedClassPolynomials.programJ 23 4 4) p118 j_expression h118
  hji := StagedExprCompile.compile_of_identity e295 (NestedReciprocal.homogenize (NestedClassPolynomials.programJ 23 4 4)).2 p295 j_inverse_expression h295
  hdj := j_degree
}
#print axioms pack
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00CompositionalNormPack
