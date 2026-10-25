/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode289
import Proofs.RadenkovicGutmanD8Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[256,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[7680,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[105728,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[885248,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[5037568,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[20624896,256,0],[256,0],[0]],[[0,0,0],[0,0],[0]],[[62741248,5632,0],[5632,0],[0]],[[0,0,0],[0,0],[0]],[[144415232,55040,0],[55040,0],[0]],[[0,0,0],[0,0],[0]],[[253778432,314880,0],[314880,0],[0]],[[0,0,0],[0,0],[0]],[[341064192,1170176,0],[1170176,0],[0]],[[0,0,0],[0,0],[0]],[[348848896,2964480,64],[2964480,128],[64]],[[0,0,0],[0,0],[0]],[[268273152,5229056,896],[5229056,1792],[896]],[[0,0,0],[0,0],[0]],[[151801344,6446080,5184],[6446080,10368],[5184]],[[0,0,0],[0,0],[0]],[[60977664,5491456,16000],[5491456,32000],[16000]],[[0,0,0],[0,0],[0]],[[16360704,3141120,28416],[3141120,56832],[28416]],[[0,0,0],[0,0],[0]],[[2612736,1140480,29312],[1140480,58624],[29312]],[[0,0,0],[0,0],[0]],[[186624,235008,16960],[235008,33920],[16960]],[[0,0,0],[0,0],[0]],[[0,20736,4992],[20736,9984],[4992]],[[0,0,0],[0,0],[0]],[[0,0,576],[0,1152],[576]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
