/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode030
import Proofs.RadenkovicGutmanD28Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e033 : NestedArithmetic.Expr 3 := .times e030 e032
noncomputable def p033 : NestedHorner.Poly 3 := [[[0],[0,28]],[[0,0],[0]],[[-252,252],[252]],[[0,0],[0]],[[84,672],[672]],[[0,0],[0]],[[4676,616],[616]],[[0,0],[0]],[[14392,224],[224]],[[0,0],[0]],[[21168,28],[28]],[[0]],[[17808]],[[0]],[[8932]],[[0]],[[2632]],[[0]],[[420]],[[0]],[[28]]]
theorem step033 : p033=NestedArithmetic.mul p030 p032 := by decide +kernel
#print axioms step033
theorem h033 : NestedArithmetic.compile e033=p033 := StagedExprCompile.compile_times e033 e030 e032 p030 p032 p033 rfl h030 h032 step033
#print axioms h033
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
