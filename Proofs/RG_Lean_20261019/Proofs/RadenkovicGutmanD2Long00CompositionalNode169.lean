/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode017
import Proofs.RadenkovicGutmanD2Long00CompositionalNode168
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e169 : NestedArithmetic.Expr 3 := .times e017 e168
noncomputable def p169 : NestedHorner.Poly 3 := [[[4],[0]],[[0,0],[0]],[[60,0],[0]],[[0,0],[0]],[[376,0],[0]],[[0,0],[0]],[[1276,0],[0]],[[0,0],[0]],[[2544,0],[0]],[[0,0],[0]],[[3028,2],[2]],[[0,0],[0]],[[2088,14],[14]],[[0,0],[0]],[[756,32],[32]],[[0,0],[0]],[[108,26],[26]],[[0,0],[0]],[[0,6],[6]]]
theorem step169 : p169=NestedArithmetic.mul p017 p168 := by decide +kernel
#print axioms step169
theorem h169 : NestedArithmetic.compile e169=p169 := StagedExprCompile.compile_times e169 e017 e168 p017 p168 p169 rfl h017 h168 step169
#print axioms h169
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
