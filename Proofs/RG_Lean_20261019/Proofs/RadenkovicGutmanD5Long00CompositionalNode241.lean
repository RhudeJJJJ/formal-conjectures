/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode240
import Proofs.RadenkovicGutmanD5Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e241 : NestedArithmetic.Expr 3 := .times e240 e001
noncomputable def p241 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[25,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[825,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[12525,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[116000,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[732750,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[3343925,25,0],[25,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11392675,600,0],[600,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[29534200,6425,0],[6425,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[58844250,40500,0],[40500,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[90403350,166975,0],[166975,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[106823475,473250,0],[473250,25,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[96277900,943700,0],[943700,350,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[65194350,1332900,0],[1332900,2025,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[32378225,1325425,0],[1325425,6250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11356125,910800,0],[910800,11100,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2643300,417875,0],[417875,11450,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[363825,120600,0],[120600,6625,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[22275,19575,0],[19575,1950,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,1350,0],[1350,225,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step241 : p241=NestedArithmetic.mul p240 p001 := by decide +kernel
#print axioms step241
theorem h241 : NestedArithmetic.compile e241=p241 := StagedExprCompile.compile_times e241 e240 e001 p240 p001 p241 rfl h240 h001 step241
#print axioms h241
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
