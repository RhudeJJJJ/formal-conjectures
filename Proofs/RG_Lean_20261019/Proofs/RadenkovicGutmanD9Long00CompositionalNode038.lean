/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode037
import Proofs.RadenkovicGutmanD9Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-7]],[[0,0],[0]],[[63,-63],[-63]],[[0,0],[0]],[[-21,-168],[-168]],[[0,0],[0]],[[-1169,-154],[-154]],[[0,0],[0]],[[-3598,-56],[-56]],[[0,0],[0]],[[-5292,-7],[-7]],[[0]],[[-4452]],[[0]],[[-2233]],[[0]],[[-658]],[[0]],[[-105]],[[0]],[[-7]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
