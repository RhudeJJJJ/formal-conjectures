/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode184
import Proofs.RadenkovicGutmanD26Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[26,0],[0]],[[0,0],[0]],[[416,0],[0]],[[0,0],[0]],[[2782,0],[0]],[[0,0],[0]],[[10088,0],[0]],[[0,0],[0]],[[21528,0],[0]],[[0,0],[0]],[[27456,26],[26]],[[0,0],[0]],[[20254,182],[182]],[[0,0],[0]],[[7800,416],[416]],[[0,0],[0]],[[1170,338],[338]],[[0,0],[0]],[[0,78],[78]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
