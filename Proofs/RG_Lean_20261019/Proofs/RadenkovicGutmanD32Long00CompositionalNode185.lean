/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode184
import Proofs.RadenkovicGutmanD32Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[32,0],[0]],[[0,0],[0]],[[512,0],[0]],[[0,0],[0]],[[3424,0],[0]],[[0,0],[0]],[[12416,0],[0]],[[0,0],[0]],[[26496,0],[0]],[[0,0],[0]],[[33792,32],[32]],[[0,0],[0]],[[24928,224],[224]],[[0,0],[0]],[[9600,512],[512]],[[0,0],[0]],[[1440,416],[416]],[[0,0],[0]],[[0,96],[96]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
