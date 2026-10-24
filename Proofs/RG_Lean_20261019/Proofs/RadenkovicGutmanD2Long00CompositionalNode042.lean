/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode040
import Proofs.RadenkovicGutmanD2Long00CompositionalNode041
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e042 : NestedArithmetic.Expr 3 := .plus e040 e041
noncomputable def p042 : NestedHorner.Poly 3 := [[[0],[0]],[[0,6],[6,0]],[[0,0],[0]],[[180,26],[26]],[[0,0],[0]],[[1380,32],[32]],[[0,0],[0]],[[4208,14],[14]],[[0,0],[0]],[[6692,2],[2]],[[0,0],[0]],[[6096,0],[0]],[[0]],[[3276]],[[0]],[[1024]],[[0]],[[172]],[[0]],[[12]],[[0]],[[0]]]
theorem step042 : p042=NestedHorner.add p040 p041 := by decide +kernel
#print axioms step042
theorem h042 : NestedArithmetic.compile e042=p042 := StagedExprCompile.compile_plus e042 e040 e041 p040 p041 p042 rfl h040 h041 step042
#print axioms h042
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
