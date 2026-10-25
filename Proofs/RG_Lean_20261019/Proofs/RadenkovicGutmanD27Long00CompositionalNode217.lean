/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode034
import Proofs.RadenkovicGutmanD27Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-54],[0]],[[0,0],[0]],[[-810,0],[0]],[[0,0],[0]],[[-5076,0],[0]],[[0,0],[0]],[[-17226,0],[0]],[[0,0],[0]],[[-34344,0],[0]],[[0,0],[0]],[[-40878,-27],[-27]],[[0,0],[0]],[[-28188,-189],[-189]],[[0,0],[0]],[[-10206,-432],[-432]],[[0,0],[0]],[[-1458,-351],[-351]],[[0,0],[0]],[[0,-81],[-81]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
