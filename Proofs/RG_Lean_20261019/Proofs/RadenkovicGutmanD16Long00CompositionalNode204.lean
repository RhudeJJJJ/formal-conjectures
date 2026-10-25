/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode194
import Proofs.RadenkovicGutmanD16Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[32],[0]],[[0,0],[0]],[[512,0],[0]],[[0,0],[0]],[[3424,0],[0]],[[0,0],[0]],[[12416,0],[0]],[[0,0],[0]],[[26496,0],[0]],[[0,0],[0]],[[33792,32],[32]],[[0,0],[0]],[[24928,224],[224]],[[0,0],[0]],[[9600,512],[512]],[[0,0],[0]],[[1440,416],[416]],[[0,0],[0]],[[0,96],[96]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
