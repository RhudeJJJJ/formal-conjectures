/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode195
import Proofs.RadenkovicGutmanD18Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[72,0],[0]],[[0,0],[0]],[[1080,0],[0]],[[0,0],[0]],[[6768,0],[0]],[[0,0],[0]],[[22968,0],[0]],[[0,0],[0]],[[45792,0],[0]],[[0,0],[0]],[[54504,36],[36]],[[0,0],[0]],[[37584,252],[252]],[[0,0],[0]],[[13608,576],[576]],[[0,0],[0]],[[1944,468],[468]],[[0,0],[0]],[[0,108],[108]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
