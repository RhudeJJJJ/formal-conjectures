/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode034
import Proofs.RadenkovicGutmanD33Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-33],[0]],[[0,0],[0]],[[-528,0],[0]],[[0,0],[0]],[[-3531,0],[0]],[[0,0],[0]],[[-12804,0],[0]],[[0,0],[0]],[[-27324,0],[0]],[[0,0],[0]],[[-34848,-33],[-33]],[[0,0],[0]],[[-25707,-231],[-231]],[[0,0],[0]],[[-9900,-528],[-528]],[[0,0],[0]],[[-1485,-429],[-429]],[[0,0],[0]],[[0,-99],[-99]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
