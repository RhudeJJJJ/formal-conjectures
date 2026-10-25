/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode204
import Proofs.RadenkovicGutmanD16Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[32,0],[0]],[[0,0],[0]],[[512,0],[0]],[[0,0],[0]],[[3424,0],[0]],[[0,0],[0]],[[12416,0],[0]],[[0,0],[0]],[[26496,0],[0]],[[0,0],[0]],[[33792,32],[32]],[[0,0],[0]],[[24928,224],[224]],[[0,0],[0]],[[9600,512],[512]],[[0,0],[0]],[[1440,416],[416]],[[0,0],[0]],[[0,96],[96]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
