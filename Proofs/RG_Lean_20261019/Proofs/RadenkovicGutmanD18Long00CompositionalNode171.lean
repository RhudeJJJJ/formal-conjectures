/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode030
import Proofs.RadenkovicGutmanD18Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[36],[0]],[[0,0],[0]],[[540,0],[0]],[[0,0],[0]],[[3384,0],[0]],[[0,0],[0]],[[11484,0],[0]],[[0,0],[0]],[[22896,0],[0]],[[0,0],[0]],[[27252,18],[18]],[[0,0],[0]],[[18792,126],[126]],[[0,0],[0]],[[6804,288],[288]],[[0,0],[0]],[[972,234],[234]],[[0,0],[0]],[[0,54],[54]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
