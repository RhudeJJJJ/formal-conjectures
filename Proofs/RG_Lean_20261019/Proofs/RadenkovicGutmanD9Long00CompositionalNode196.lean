/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode195
import Proofs.RadenkovicGutmanD9Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[36,0],[0]],[[0,0],[0]],[[540,0],[0]],[[0,0],[0]],[[3384,0],[0]],[[0,0],[0]],[[11484,0],[0]],[[0,0],[0]],[[22896,0],[0]],[[0,0],[0]],[[27252,18],[18]],[[0,0],[0]],[[18792,126],[126]],[[0,0],[0]],[[6804,288],[288]],[[0,0],[0]],[[972,234],[234]],[[0,0],[0]],[[0,54],[54]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
