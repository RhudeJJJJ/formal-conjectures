/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode195
import Proofs.RadenkovicGutmanD38Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[152,0],[0]],[[0,0],[0]],[[2280,0],[0]],[[0,0],[0]],[[14288,0],[0]],[[0,0],[0]],[[48488,0],[0]],[[0,0],[0]],[[96672,0],[0]],[[0,0],[0]],[[115064,76],[76]],[[0,0],[0]],[[79344,532],[532]],[[0,0],[0]],[[28728,1216],[1216]],[[0,0],[0]],[[4104,988],[988]],[[0,0],[0]],[[0,228],[228]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
