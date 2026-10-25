/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode195
import Proofs.RadenkovicGutmanD40Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[160,0],[0]],[[0,0],[0]],[[2400,0],[0]],[[0,0],[0]],[[15040,0],[0]],[[0,0],[0]],[[51040,0],[0]],[[0,0],[0]],[[101760,0],[0]],[[0,0],[0]],[[121120,80],[80]],[[0,0],[0]],[[83520,560],[560]],[[0,0],[0]],[[30240,1280],[1280]],[[0,0],[0]],[[4320,1040],[1040]],[[0,0],[0]],[[0,240],[240]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
