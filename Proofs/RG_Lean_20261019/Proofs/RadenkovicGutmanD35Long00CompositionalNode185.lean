/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode184
import Proofs.RadenkovicGutmanD35Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[35,0],[0]],[[0,0],[0]],[[560,0],[0]],[[0,0],[0]],[[3745,0],[0]],[[0,0],[0]],[[13580,0],[0]],[[0,0],[0]],[[28980,0],[0]],[[0,0],[0]],[[36960,35],[35]],[[0,0],[0]],[[27265,245],[245]],[[0,0],[0]],[[10500,560],[560]],[[0,0],[0]],[[1575,455],[455]],[[0,0],[0]],[[0,105],[105]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
