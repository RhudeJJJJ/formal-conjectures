/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode034
import Proofs.RadenkovicGutmanD9Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-9],[0]],[[0,0],[0]],[[-144,0],[0]],[[0,0],[0]],[[-963,0],[0]],[[0,0],[0]],[[-3492,0],[0]],[[0,0],[0]],[[-7452,0],[0]],[[0,0],[0]],[[-9504,-9],[-9]],[[0,0],[0]],[[-7011,-63],[-63]],[[0,0],[0]],[[-2700,-144],[-144]],[[0,0],[0]],[[-405,-117],[-117]],[[0,0],[0]],[[0,-27],[-27]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
