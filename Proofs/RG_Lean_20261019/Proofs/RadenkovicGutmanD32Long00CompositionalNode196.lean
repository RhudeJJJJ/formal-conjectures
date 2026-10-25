/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode195
import Proofs.RadenkovicGutmanD32Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[128,0],[0]],[[0,0],[0]],[[1920,0],[0]],[[0,0],[0]],[[12032,0],[0]],[[0,0],[0]],[[40832,0],[0]],[[0,0],[0]],[[81408,0],[0]],[[0,0],[0]],[[96896,64],[64]],[[0,0],[0]],[[66816,448],[448]],[[0,0],[0]],[[24192,1024],[1024]],[[0,0],[0]],[[3456,832],[832]],[[0,0],[0]],[[0,192],[192]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
