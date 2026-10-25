/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode065
import Proofs.RadenkovicGutmanD32Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[32],[0]],[[0,0],[0]],[[512,0],[0]],[[0,0],[0]],[[3424,0],[0]],[[0,0],[0]],[[12416,0],[0]],[[0,0],[0]],[[26496,0],[0]],[[0,0],[0]],[[33792,32],[32]],[[0,0],[0]],[[24928,224],[224]],[[0,0],[0]],[[9600,512],[512]],[[0,0],[0]],[[1440,416],[416]],[[0,0],[0]],[[0,96],[96]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
