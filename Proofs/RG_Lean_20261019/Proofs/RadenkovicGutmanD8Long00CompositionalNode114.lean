/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,576],[0,1152],[576]],[[0,0,0],[0,0],[0]],[[0,20736,4992],[20736,9984],[4992]],[[0,0,0],[0,0],[0]],[[186624,235008,16960],[235008,33920],[16960]],[[0,0,0],[0,0],[0]],[[2612736,1140480,29312],[1140480,58624],[29312]],[[0,0,0],[0,0],[0]],[[16360704,3141120,28416],[3141120,56832],[28416]],[[0,0,0],[0,0],[0]],[[60977664,5491456,16000],[5491456,32000],[16000]],[[0,0,0],[0,0],[0]],[[151801344,6446080,5184],[6446080,10368],[5184]],[[0,0,0],[0,0],[0]],[[268273152,5229056,896],[5229056,1792],[896]],[[0,0,0],[0,0],[0]],[[348848896,2964480,64],[2964480,128],[64]],[[0,0],[0]],[[341064192,1170176],[1170176]],[[0,0],[0]],[[253778432,314880],[314880]],[[0,0],[0]],[[144415232,55040],[55040]],[[0,0],[0]],[[62741248,5632],[5632]],[[0,0],[0]],[[20624896,256],[256]],[[0]],[[5037568]],[[0]],[[885248]],[[0]],[[105728]],[[0]],[[7680]],[[0]],[[256]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
