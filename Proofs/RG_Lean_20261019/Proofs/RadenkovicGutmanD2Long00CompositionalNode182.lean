/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode017
import Proofs.RadenkovicGutmanD2Long00CompositionalNode181
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e182 : NestedArithmetic.Expr 3 := .times e017 e181
noncomputable def p182 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[32,0],[0]],[[0,0],[0]],[[214,0],[0]],[[0,0],[0]],[[776,0],[0]],[[0,0],[0]],[[1656,0],[0]],[[0,0],[0]],[[2112,2],[2]],[[0,0],[0]],[[1558,14],[14]],[[0,0],[0]],[[600,32],[32]],[[0,0],[0]],[[90,26],[26]],[[0,0],[0]],[[0,6],[6]]]
theorem step182 : p182=NestedArithmetic.mul p017 p181 := by decide +kernel
#print axioms step182
theorem h182 : NestedArithmetic.compile e182=p182 := StagedExprCompile.compile_times e182 e017 e181 p017 p181 p182 rfl h017 h181 step182
#print axioms h182
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
