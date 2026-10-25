/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode034
import Proofs.RadenkovicGutmanD10Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-160,0],[0]],[[0,0],[0]],[[-1070,0],[0]],[[0,0],[0]],[[-3880,0],[0]],[[0,0],[0]],[[-8280,0],[0]],[[0,0],[0]],[[-10560,-10],[-10]],[[0,0],[0]],[[-7790,-70],[-70]],[[0,0],[0]],[[-3000,-160],[-160]],[[0,0],[0]],[[-450,-130],[-130]],[[0,0],[0]],[[0,-30],[-30]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
