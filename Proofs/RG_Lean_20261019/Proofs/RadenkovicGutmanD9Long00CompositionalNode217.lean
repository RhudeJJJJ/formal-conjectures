/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode034
import Proofs.RadenkovicGutmanD9Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-270,0],[0]],[[0,0],[0]],[[-1692,0],[0]],[[0,0],[0]],[[-5742,0],[0]],[[0,0],[0]],[[-11448,0],[0]],[[0,0],[0]],[[-13626,-9],[-9]],[[0,0],[0]],[[-9396,-63],[-63]],[[0,0],[0]],[[-3402,-144],[-144]],[[0,0],[0]],[[-486,-117],[-117]],[[0,0],[0]],[[0,-27],[-27]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
