/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode194
import Proofs.RadenkovicGutmanD17Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[34],[0]],[[0,0],[0]],[[544,0],[0]],[[0,0],[0]],[[3638,0],[0]],[[0,0],[0]],[[13192,0],[0]],[[0,0],[0]],[[28152,0],[0]],[[0,0],[0]],[[35904,34],[34]],[[0,0],[0]],[[26486,238],[238]],[[0,0],[0]],[[10200,544],[544]],[[0,0],[0]],[[1530,442],[442]],[[0,0],[0]],[[0,102],[102]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
