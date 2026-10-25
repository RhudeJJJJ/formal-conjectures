/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode184
import Proofs.RadenkovicGutmanD22Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[22,0],[0]],[[0,0],[0]],[[352,0],[0]],[[0,0],[0]],[[2354,0],[0]],[[0,0],[0]],[[8536,0],[0]],[[0,0],[0]],[[18216,0],[0]],[[0,0],[0]],[[23232,22],[22]],[[0,0],[0]],[[17138,154],[154]],[[0,0],[0]],[[6600,352],[352]],[[0,0],[0]],[[990,286],[286]],[[0,0],[0]],[[0,66],[66]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
