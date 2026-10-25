/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode164
import Proofs.RadenkovicGutmanD34Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-64],[0]],[[0,0],[0]],[[-952,0],[0,0]],[[0,0],[0,0]],[[-5904,0],[0,0]],[[0,0],[0,0]],[[-19768,0],[0,0]],[[0,0],[0,0]],[[-38704,0],[0,0]],[[0,0],[0,0]],[[-44832,-64],[-64,0]],[[0,0],[0,0]],[[-29232,-512],[-512,0]],[[0,0],[0,0]],[[-8568,-1408],[-1408,0]],[[0,0],[0,0]],[[432,-1536],[-1536,0]],[[0,0],[0,0]],[[648,-576],[-576,0]],[[0],[0,0]],[[0],[0,-64]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
