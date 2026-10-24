/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
import Proofs.RadenkovicGutmanStagedExprCompile
import Proofs.RadenkovicGutmanExprDecidableEquality
import Proofs.RadenkovicGutmanD4Long00CompositionalNode087
import Proofs.RadenkovicGutmanD4Long00CompositionalNode108
import Proofs.RadenkovicGutmanD4Long00CompositionalNode117
import Proofs.RadenkovicGutmanD4Long00CompositionalNode243
import Proofs.RadenkovicGutmanD4Long00CompositionalNode278
import Proofs.RadenkovicGutmanD4Long00CompositionalNode293
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00CompositionalNormPack
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open FixedDegree04Long00Compositional
theorem u_expression : e087=NestedClassPolynomials.programU 4 4 4 := by decide +kernel
#print axioms u_expression
theorem u_inverse_expression : e243=(NestedReciprocal.homogenize (NestedClassPolynomials.programU 4 4 4)).2 := by decide +kernel
#print axioms u_inverse_expression
theorem u_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programU 4 4 4)).1=88 := by decide +kernel
#print axioms u_degree
noncomputable def u : NestedHorner.Poly 3 := p087
noncomputable def ui : NestedHorner.Poly 3 := p243
theorem v_expression : e108=NestedClassPolynomials.programV 4 4 4 := by decide +kernel
#print axioms v_expression
theorem v_inverse_expression : e278=(NestedReciprocal.homogenize (NestedClassPolynomials.programV 4 4 4)).2 := by decide +kernel
#print axioms v_inverse_expression
theorem v_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programV 4 4 4)).1=84 := by decide +kernel
#print axioms v_degree
noncomputable def v : NestedHorner.Poly 3 := p108
noncomputable def vi : NestedHorner.Poly 3 := p278
theorem j_expression : e117=NestedClassPolynomials.programJ 4 4 4 := by decide +kernel
#print axioms j_expression
theorem j_inverse_expression : e293=(NestedReciprocal.homogenize (NestedClassPolynomials.programJ 4 4 4)).2 := by decide +kernel
#print axioms j_inverse_expression
theorem j_degree : (NestedReciprocal.homogenize (NestedClassPolynomials.programJ 4 4 4)).1=88 := by decide +kernel
#print axioms j_degree
noncomputable def j : NestedHorner.Poly 3 := p117
noncomputable def ji : NestedHorner.Poly 3 := p293
noncomputable def pack : NormProgramPack.Pack 4 4 4 := {
  u := u
  ui := ui
  du := 88
  v := v
  vi := vi
  dv := 84
  j := j
  ji := ji
  dj := 88
  hu := StagedExprCompile.compile_of_identity e087 (NestedClassPolynomials.programU 4 4 4) p087 u_expression h087
  hui := StagedExprCompile.compile_of_identity e243 (NestedReciprocal.homogenize (NestedClassPolynomials.programU 4 4 4)).2 p243 u_inverse_expression h243
  hdu := u_degree
  hv := StagedExprCompile.compile_of_identity e108 (NestedClassPolynomials.programV 4 4 4) p108 v_expression h108
  hvi := StagedExprCompile.compile_of_identity e278 (NestedReciprocal.homogenize (NestedClassPolynomials.programV 4 4 4)).2 p278 v_inverse_expression h278
  hdv := v_degree
  hj := StagedExprCompile.compile_of_identity e117 (NestedClassPolynomials.programJ 4 4 4) p117 j_expression h117
  hji := StagedExprCompile.compile_of_identity e293 (NestedReciprocal.homogenize (NestedClassPolynomials.programJ 4 4 4)).2 p293 j_inverse_expression h293
  hdj := j_degree
}
#print axioms pack
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00CompositionalNormPack
