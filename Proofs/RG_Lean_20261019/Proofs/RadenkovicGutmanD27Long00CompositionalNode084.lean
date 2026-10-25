/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,39366,0],[39366,6561,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[649539,570807,0],[570807,56862,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[10609137,3516696,0],[3516696,193185,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[77078628,12185235,0],[12185235,333882,0],[0,0]],[[0,0,0],[0,0],[0]],[[331144605,26558928,0],[26558928,323676],[0]],[[0,0,0],[0,0],[0]],[[944149041,38649393,0],[38649393,182250],[0]],[[0,0,0],[0,0],[0]],[[1901067246,38867364,0],[38867364,59049],[0]],[[0,0,0],[0,0],[0]],[[2807463564,27518292,0],[27518292,10206],[0]],[[0,0,0],[0,0],[0]],[[3114972531,13799970,0],[13799970,729],[0]],[[0,0],[0]],[[2636161686,4868991],[4868991]],[[0,0],[0]],[[1715898330,1180980],[1180980]],[[0,0],[0]],[[861217272,187353],[187353]],[[0,0],[0]],[[332210403,17496],[17496]],[[0,0],[0]],[[97508853,729],[729]],[[0]],[[21366990]],[[0]],[[3382560]],[[0]],[[365229]],[[0]],[[24057]],[[0]],[[729]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
