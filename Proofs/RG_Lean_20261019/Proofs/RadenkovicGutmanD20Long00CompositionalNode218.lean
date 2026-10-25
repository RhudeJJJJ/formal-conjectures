/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode034
import Proofs.RadenkovicGutmanD20Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-20],[0]],[[0,0],[0]],[[-320,0],[0]],[[0,0],[0]],[[-2140,0],[0]],[[0,0],[0]],[[-7760,0],[0]],[[0,0],[0]],[[-16560,0],[0]],[[0,0],[0]],[[-21120,-20],[-20]],[[0,0],[0]],[[-15580,-140],[-140]],[[0,0],[0]],[[-6000,-320],[-320]],[[0,0],[0]],[[-900,-260],[-260]],[[0,0],[0]],[[0,-60],[-60]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
