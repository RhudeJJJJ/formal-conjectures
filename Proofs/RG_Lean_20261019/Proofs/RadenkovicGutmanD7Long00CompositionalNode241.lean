/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode240
import Proofs.RadenkovicGutmanD7Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e241 : NestedArithmetic.Expr 3 := .times e240 e001
noncomputable def p241 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[49,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1617,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[24549,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[227360,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1436190,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[6554093,49,0],[49,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[22329643,1176,0],[1176,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[57887032,12593,0],[12593,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[115334730,79380,0],[79380,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[177190566,327271,0],[327271,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[209374011,927570,0],[927570,49,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[188704684,1849652,0],[1849652,686,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[127780926,2612484,0],[2612484,3969,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[63461321,2597833,0],[2597833,12250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[22258005,1785168,0],[1785168,21756,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5180868,819035,0],[819035,22442,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[713097,236376,0],[236376,12985,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[43659,38367,0],[38367,3822,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,2646,0],[2646,441,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step241 : p241=NestedArithmetic.mul p240 p001 := by decide +kernel
#print axioms step241
theorem h241 : NestedArithmetic.compile e241=p241 := StagedExprCompile.compile_times e241 e240 e001 p240 p001 p241 rfl h240 h001 step241
#print axioms h241
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
