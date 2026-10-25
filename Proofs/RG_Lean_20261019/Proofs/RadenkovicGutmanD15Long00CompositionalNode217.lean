/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode034
import Proofs.RadenkovicGutmanD15Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-450,0],[0]],[[0,0],[0]],[[-2820,0],[0]],[[0,0],[0]],[[-9570,0],[0]],[[0,0],[0]],[[-19080,0],[0]],[[0,0],[0]],[[-22710,-15],[-15]],[[0,0],[0]],[[-15660,-105],[-105]],[[0,0],[0]],[[-5670,-240],[-240]],[[0,0],[0]],[[-810,-195],[-195]],[[0,0],[0]],[[0,-45],[-45]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
