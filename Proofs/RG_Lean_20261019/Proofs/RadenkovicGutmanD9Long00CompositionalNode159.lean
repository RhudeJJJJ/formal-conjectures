/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode037
import Proofs.RadenkovicGutmanD9Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-7],[0]],[[0,0],[0]],[[-105,0],[0,0]],[[0,0],[0,0]],[[-658,0],[0,0]],[[0,0],[0,0]],[[-2233,0],[0,0]],[[0,0],[0,0]],[[-4452,0],[0,0]],[[0,0],[0,0]],[[-5292,-7],[-7,0]],[[0,0],[0,0]],[[-3598,-56],[-56,0]],[[0,0],[0,0]],[[-1169,-154],[-154,0]],[[0,0],[0,0]],[[-21,-168],[-168,0]],[[0,0],[0,0]],[[63,-63],[-63,0]],[[0],[0,0]],[[0],[0,-7]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
