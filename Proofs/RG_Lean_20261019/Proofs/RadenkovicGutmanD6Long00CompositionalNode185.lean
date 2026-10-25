/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode184
import Proofs.RadenkovicGutmanD6Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[6,0],[0]],[[0,0],[0]],[[96,0],[0]],[[0,0],[0]],[[642,0],[0]],[[0,0],[0]],[[2328,0],[0]],[[0,0],[0]],[[4968,0],[0]],[[0,0],[0]],[[6336,6],[6]],[[0,0],[0]],[[4674,42],[42]],[[0,0],[0]],[[1800,96],[96]],[[0,0],[0]],[[270,78],[78]],[[0,0],[0]],[[0,18],[18]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
