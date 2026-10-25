/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode184
import Proofs.RadenkovicGutmanD30Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[30,0],[0]],[[0,0],[0]],[[480,0],[0]],[[0,0],[0]],[[3210,0],[0]],[[0,0],[0]],[[11640,0],[0]],[[0,0],[0]],[[24840,0],[0]],[[0,0],[0]],[[31680,30],[30]],[[0,0],[0]],[[23370,210],[210]],[[0,0],[0]],[[9000,480],[480]],[[0,0],[0]],[[1350,390],[390]],[[0,0],[0]],[[0,90],[90]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
