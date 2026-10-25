/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode171
import Proofs.RadenkovicGutmanD18Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[36,0],[0]],[[0,0],[0]],[[540,0],[0]],[[0,0],[0]],[[3384,0],[0]],[[0,0],[0]],[[11484,0],[0]],[[0,0],[0]],[[22896,0],[0]],[[0,0],[0]],[[27252,18],[18]],[[0,0],[0]],[[18792,126],[126]],[[0,0],[0]],[[6804,288],[288]],[[0,0],[0]],[[972,234],[234]],[[0,0],[0]],[[0,54],[54]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
