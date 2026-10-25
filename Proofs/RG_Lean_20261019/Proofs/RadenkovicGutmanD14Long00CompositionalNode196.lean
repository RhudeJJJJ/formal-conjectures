/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode195
import Proofs.RadenkovicGutmanD14Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[56,0],[0]],[[0,0],[0]],[[840,0],[0]],[[0,0],[0]],[[5264,0],[0]],[[0,0],[0]],[[17864,0],[0]],[[0,0],[0]],[[35616,0],[0]],[[0,0],[0]],[[42392,28],[28]],[[0,0],[0]],[[29232,196],[196]],[[0,0],[0]],[[10584,448],[448]],[[0,0],[0]],[[1512,364],[364]],[[0,0],[0]],[[0,84],[84]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
