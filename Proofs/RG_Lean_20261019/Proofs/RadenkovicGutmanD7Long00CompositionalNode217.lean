/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode034
import Proofs.RadenkovicGutmanD7Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-14],[0]],[[0,0],[0]],[[-210,0],[0]],[[0,0],[0]],[[-1316,0],[0]],[[0,0],[0]],[[-4466,0],[0]],[[0,0],[0]],[[-8904,0],[0]],[[0,0],[0]],[[-10598,-7],[-7]],[[0,0],[0]],[[-7308,-49],[-49]],[[0,0],[0]],[[-2646,-112],[-112]],[[0,0],[0]],[[-378,-91],[-91]],[[0,0],[0]],[[0,-21],[-21]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
