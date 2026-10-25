/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode159
import Proofs.RadenkovicGutmanD9Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-7],[0]],[[0,0],[0]],[[-105,0],[0,0]],[[0,0],[0,0]],[[-658,0],[0,0]],[[0,0],[0,0]],[[-2233,0],[0,0]],[[0,0],[0,0]],[[-4452,0],[0,0]],[[0,0],[0,0]],[[-5292,-7],[-7,0]],[[0,0],[0,0]],[[-3598,-56],[-56,0]],[[0,0],[0,0]],[[-1169,-154],[-154,0]],[[0,0],[0,0]],[[-21,-168],[-168,0]],[[0,0],[0,0]],[[63,-63],[-63,0]],[[0],[0,0]],[[0],[0,-7]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
