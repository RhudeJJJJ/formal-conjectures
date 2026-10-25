/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,12150,0],[12150,2025,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[200475,176175,0],[176175,17550,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[3274425,1085400,0],[1085400,59625,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[23789700,3760875,0],[3760875,103050,0],[0,0]],[[0,0,0],[0,0],[0]],[[102205125,8197200,0],[8197200,99900],[0]],[[0,0,0],[0,0],[0]],[[291404025,11928825,0],[11928825,56250],[0]],[[0,0,0],[0,0],[0]],[[586749150,11996100,0],[11996100,18225],[0]],[[0,0,0],[0,0],[0]],[[866501100,8493300,0],[8493300,3150],[0]],[[0,0,0],[0,0],[0]],[[961411275,4259250,0],[4259250,225],[0]],[[0,0],[0]],[[813630150,1502775],[1502775]],[[0,0],[0]],[[529598250,364500],[364500]],[[0,0],[0]],[[265807800,57825],[57825]],[[0,0],[0]],[[102534075,5400],[5400]],[[0,0],[0]],[[30095325,225],[225]],[[0]],[[6594750]],[[0]],[[1044000]],[[0]],[[112725]],[[0]],[[7425]],[[0]],[[225]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
