/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode204
import Proofs.RadenkovicGutmanD17Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[34,0],[0]],[[0,0],[0]],[[544,0],[0]],[[0,0],[0]],[[3638,0],[0]],[[0,0],[0]],[[13192,0],[0]],[[0,0],[0]],[[28152,0],[0]],[[0,0],[0]],[[35904,34],[34]],[[0,0],[0]],[[26486,238],[238]],[[0,0],[0]],[[10200,544],[544]],[[0,0],[0]],[[1530,442],[442]],[[0,0],[0]],[[0,102],[102]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
