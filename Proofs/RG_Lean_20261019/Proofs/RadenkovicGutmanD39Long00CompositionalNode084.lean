/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,82134,0],[82134,13689,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1355211,1190943,0],[1190943,118638,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[22135113,7337304,0],[7337304,403065,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[160818372,25423515,0],[25423515,696618,0],[0,0]],[[0,0,0],[0,0],[0]],[[690906645,55413072,0],[55413072,675324],[0]],[[0,0,0],[0,0],[0]],[[1969891209,80638857,0],[80638857,380250],[0]],[[0,0,0],[0,0],[0]],[[3966424254,81093636,0],[81093636,123201],[0]],[[0,0,0],[0,0],[0]],[[5857547436,57414708,0],[57414708,21294],[0]],[[0,0,0],[0,0],[0]],[[6499140219,28792530,0],[28792530,1521],[0]],[[0,0],[0]],[[5500139814,10158759],[10158759]],[[0,0],[0]],[[3580084170,2464020],[2464020]],[[0,0],[0]],[[1796860728,390897],[390897]],[[0,0],[0]],[[693130347,36504],[36504]],[[0,0],[0]],[[203444397,1521],[1521]],[[0]],[[44580510]],[[0]],[[7057440]],[[0]],[[762021]],[[0]],[[50193]],[[0]],[[1521]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
