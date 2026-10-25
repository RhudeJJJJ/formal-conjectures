/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode034
import Proofs.RadenkovicGutmanD8Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-240,0],[0]],[[0,0],[0]],[[-1504,0],[0]],[[0,0],[0]],[[-5104,0],[0]],[[0,0],[0]],[[-10176,0],[0]],[[0,0],[0]],[[-12112,-8],[-8]],[[0,0],[0]],[[-8352,-56],[-56]],[[0,0],[0]],[[-3024,-128],[-128]],[[0,0],[0]],[[-432,-104],[-104]],[[0,0],[0]],[[0,-24],[-24]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
