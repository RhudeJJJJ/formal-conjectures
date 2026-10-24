/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,1350,0],[1350,225,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[22275,19575,0],[19575,1950,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[363825,120600,0],[120600,6625,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2643300,417875,0],[417875,11450,0],[0,0]],[[0,0,0],[0,0],[0]],[[11356125,910800,0],[910800,11100],[0]],[[0,0,0],[0,0],[0]],[[32378225,1325425,0],[1325425,6250],[0]],[[0,0,0],[0,0],[0]],[[65194350,1332900,0],[1332900,2025],[0]],[[0,0,0],[0,0],[0]],[[96277900,943700,0],[943700,350],[0]],[[0,0,0],[0,0],[0]],[[106823475,473250,0],[473250,25],[0]],[[0,0],[0]],[[90403350,166975],[166975]],[[0,0],[0]],[[58844250,40500],[40500]],[[0,0],[0]],[[29534200,6425],[6425]],[[0,0],[0]],[[11392675,600],[600]],[[0,0],[0]],[[3343925,25],[25]],[[0]],[[732750]],[[0]],[[116000]],[[0]],[[12525]],[[0]],[[825]],[[0]],[[25]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
