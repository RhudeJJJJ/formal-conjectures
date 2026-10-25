/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode171
import Proofs.RadenkovicGutmanD30Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[60,0],[0]],[[0,0],[0]],[[900,0],[0]],[[0,0],[0]],[[5640,0],[0]],[[0,0],[0]],[[19140,0],[0]],[[0,0],[0]],[[38160,0],[0]],[[0,0],[0]],[[45420,30],[30]],[[0,0],[0]],[[31320,210],[210]],[[0,0],[0]],[[11340,480],[480]],[[0,0],[0]],[[1620,390],[390]],[[0,0],[0]],[[0,90],[90]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
