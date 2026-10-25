/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode030
import Proofs.RadenkovicGutmanD32Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[32],[0]],[[0,0],[0]],[[512,0],[0]],[[0,0],[0]],[[3424,0],[0]],[[0,0],[0]],[[12416,0],[0]],[[0,0],[0]],[[26496,0],[0]],[[0,0],[0]],[[33792,32],[32]],[[0,0],[0]],[[24928,224],[224]],[[0,0],[0]],[[9600,512],[512]],[[0,0],[0]],[[1440,416],[416]],[[0,0],[0]],[[0,96],[96]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
