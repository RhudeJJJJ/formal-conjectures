/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode176
import Proofs.RadenkovicGutmanD2Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .plus e176 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[0],[0]],[[0,0],[0]],[[2,0],[0,0]],[[0,0],[0,0]],[[32,0],[0,0]],[[0,0],[0,0]],[[214,0],[0,0]],[[0,0],[0,0]],[[776,0],[0,0]],[[0,0],[0,0]],[[1656,0],[0,0]],[[0,0],[0,0]],[[2112,2],[2,0]],[[0,0],[0,0]],[[1558,14],[14,0]],[[0,0],[0,0]],[[600,32],[32,0]],[[0,0],[0,0]],[[90,26],[26,0]],[[0,0],[0,0]],[[0,6],[6,0]]]
theorem step184 : p184=NestedHorner.add p176 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_plus e184 e176 e183 p176 p183 p184 rfl h176 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
