/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode063
import Proofs.RadenkovicGutmanD2Long00CompositionalNode215
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e216 : NestedArithmetic.Expr 3 := .times e063 e215
noncomputable def p216 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[32,0],[0]],[[0,0],[0]],[[214,0],[0]],[[0,0],[0]],[[776,0],[0]],[[0,0],[0]],[[1656,0],[0]],[[0,0],[0]],[[2112,2],[2]],[[0,0],[0]],[[1558,14],[14]],[[0,0],[0]],[[600,32],[32]],[[0,0],[0]],[[90,26],[26]],[[0,0],[0]],[[0,6],[6]]]
theorem step216 : p216=NestedArithmetic.mul p063 p215 := by decide +kernel
#print axioms step216
theorem h216 : NestedArithmetic.compile e216=p216 := StagedExprCompile.compile_times e216 e063 e215 p063 p215 p216 rfl h063 h215 step216
#print axioms h216
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
