/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode195
import Proofs.RadenkovicGutmanD27Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[108,0],[0]],[[0,0],[0]],[[1620,0],[0]],[[0,0],[0]],[[10152,0],[0]],[[0,0],[0]],[[34452,0],[0]],[[0,0],[0]],[[68688,0],[0]],[[0,0],[0]],[[81756,54],[54]],[[0,0],[0]],[[56376,378],[378]],[[0,0],[0]],[[20412,864],[864]],[[0,0],[0]],[[2916,702],[702]],[[0,0],[0]],[[0,162],[162]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
