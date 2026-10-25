/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,99846,0],[99846,16641,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1647459,1447767,0],[1447767,144222,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[26908497,8919576,0],[8919576,489985,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[195498468,30906035,0],[30906035,846842,0],[0,0]],[[0,0,0],[0,0],[0]],[[839899005,67362768,0],[67362768,820956],[0]],[[0,0,0],[0,0],[0]],[[2394693521,98028433,0],[98028433,462250],[0]],[[0,0,0],[0,0],[0]],[[4821774126,98581284,0],[98581284,149769],[0]],[[0,0,0],[0,0],[0]],[[7120713484,69796052,0],[69796052,25886],[0]],[[0,0,0],[0,0],[0]],[[7900664211,35001570,0],[35001570,1849],[0]],[[0,0],[0]],[[6686231766,12349471],[12349471]],[[0,0],[0]],[[4352120730,2995380],[2995380]],[[0,0],[0]],[[2184349432,475193],[475193]],[[0,0],[0]],[[842602243,44376],[44376]],[[0,0],[0]],[[247316693,1849],[1849]],[[0]],[[54194190]],[[0]],[[8579360]],[[0]],[[926349]],[[0]],[[61017]],[[0]],[[1849]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
