/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode195
import Proofs.RadenkovicGutmanD20Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[80,0],[0]],[[0,0],[0]],[[1200,0],[0]],[[0,0],[0]],[[7520,0],[0]],[[0,0],[0]],[[25520,0],[0]],[[0,0],[0]],[[50880,0],[0]],[[0,0],[0]],[[60560,40],[40]],[[0,0],[0]],[[41760,280],[280]],[[0,0],[0]],[[15120,640],[640]],[[0,0],[0]],[[2160,520],[520]],[[0,0],[0]],[[0,120],[120]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
