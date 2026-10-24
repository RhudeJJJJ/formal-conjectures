/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode239
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e240 : NestedArithmetic.Expr 3 := .scaled (-1) e239
noncomputable def p240 : NestedHorner.Poly 3 := [[[25],[0],[0]],[[0,0],[0,0],[0]],[[825,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[12525,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[116000,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[732750,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[3343925,25,0],[25,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11392675,600,0],[600,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[29534200,6425,0],[6425,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[58844250,40500,0],[40500,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[90403350,166975,0],[166975,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[106823475,473250,0],[473250,25,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[96277900,943700,0],[943700,350,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[65194350,1332900,0],[1332900,2025,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[32378225,1325425,0],[1325425,6250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[11356125,910800,0],[910800,11100,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2643300,417875,0],[417875,11450,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[363825,120600,0],[120600,6625,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[22275,19575,0],[19575,1950,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,1350,0],[1350,225,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step240 : p240=NestedHorner.scale (-1) p239 := by decide +kernel
#print axioms step240
theorem h240 : NestedArithmetic.compile e240=p240 := StagedExprCompile.compile_scaled (-1) e240 e239 p239 p240 rfl h239 step240
#print axioms h240
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
