/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode195
import Proofs.RadenkovicGutmanD33Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[132,0],[0]],[[0,0],[0]],[[1980,0],[0]],[[0,0],[0]],[[12408,0],[0]],[[0,0],[0]],[[42108,0],[0]],[[0,0],[0]],[[83952,0],[0]],[[0,0],[0]],[[99924,66],[66]],[[0,0],[0]],[[68904,462],[462]],[[0,0],[0]],[[24948,1056],[1056]],[[0,0],[0]],[[3564,858],[858]],[[0,0],[0]],[[0,198],[198]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
