/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode184
import Proofs.RadenkovicGutmanD34Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[34,0],[0]],[[0,0],[0]],[[544,0],[0]],[[0,0],[0]],[[3638,0],[0]],[[0,0],[0]],[[13192,0],[0]],[[0,0],[0]],[[28152,0],[0]],[[0,0],[0]],[[35904,34],[34]],[[0,0],[0]],[[26486,238],[238]],[[0,0],[0]],[[10200,544],[544]],[[0,0],[0]],[[1530,442],[442]],[[0,0],[0]],[[0,102],[102]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
