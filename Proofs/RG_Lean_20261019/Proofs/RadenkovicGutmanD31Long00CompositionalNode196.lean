/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode195
import Proofs.RadenkovicGutmanD31Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[124,0],[0]],[[0,0],[0]],[[1860,0],[0]],[[0,0],[0]],[[11656,0],[0]],[[0,0],[0]],[[39556,0],[0]],[[0,0],[0]],[[78864,0],[0]],[[0,0],[0]],[[93868,62],[62]],[[0,0],[0]],[[64728,434],[434]],[[0,0],[0]],[[23436,992],[992]],[[0,0],[0]],[[3348,806],[806]],[[0,0],[0]],[[0,186],[186]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
