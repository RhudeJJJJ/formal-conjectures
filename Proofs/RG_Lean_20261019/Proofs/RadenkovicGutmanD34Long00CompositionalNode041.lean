/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode036
import Proofs.RadenkovicGutmanD34Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-64]],[[0,0],[0]],[[648,-576],[-576]],[[0,0],[0]],[[432,-1536],[-1536]],[[0,0],[0]],[[-8568,-1408],[-1408]],[[0,0],[0]],[[-29232,-512],[-512]],[[0,0],[0]],[[-44832,-64],[-64]],[[0]],[[-38704]],[[0]],[[-19768]],[[0]],[[-5904]],[[0]],[[-952]],[[0]],[[-64]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
