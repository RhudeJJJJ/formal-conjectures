/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode119
import Proofs.RadenkovicGutmanD34Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-64],[0]],[[0,0],[0]],[[-952,0],[0,0]],[[0,0],[0,0]],[[-5904,0],[0,0]],[[0,0],[0,0]],[[-19768,0],[0,0]],[[0,0],[0,0]],[[-38704,0],[0,0]],[[0,0],[0,0]],[[-44832,-64],[-64,0]],[[0,0],[0,0]],[[-29232,-512],[-512,0]],[[0,0],[0,0]],[[-8568,-1408],[-1408,0]],[[0,0],[0,0]],[[432,-1536],[-1536,0]],[[0,0],[0,0]],[[648,-576],[-576,0]],[[0],[0,0]],[[0],[0,-64]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
