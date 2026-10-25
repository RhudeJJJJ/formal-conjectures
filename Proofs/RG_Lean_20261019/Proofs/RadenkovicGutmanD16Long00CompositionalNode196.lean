/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode195
import Proofs.RadenkovicGutmanD16Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[64,0],[0]],[[0,0],[0]],[[960,0],[0]],[[0,0],[0]],[[6016,0],[0]],[[0,0],[0]],[[20416,0],[0]],[[0,0],[0]],[[40704,0],[0]],[[0,0],[0]],[[48448,32],[32]],[[0,0],[0]],[[33408,224],[224]],[[0,0],[0]],[[12096,512],[512]],[[0,0],[0]],[[1728,416],[416]],[[0,0],[0]],[[0,96],[96]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
