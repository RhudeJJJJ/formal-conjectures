/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode017
import Proofs.RadenkovicGutmanD2Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e017 e028
noncomputable def p041 : NestedHorner.Poly 3 := [[[0],[0]],[[0,6],[6]],[[0,0],[0]],[[108,26],[26]],[[0,0],[0]],[[756,32],[32]],[[0,0],[0]],[[2088,14],[14]],[[0,0],[0]],[[3028,2],[2]],[[0]],[[2544]],[[0]],[[1276]],[[0]],[[376]],[[0]],[[60]],[[0]],[[4]]]
theorem step041 : p041=NestedArithmetic.mul p017 p028 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e017 e028 p017 p028 p041 rfl h017 h028 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
