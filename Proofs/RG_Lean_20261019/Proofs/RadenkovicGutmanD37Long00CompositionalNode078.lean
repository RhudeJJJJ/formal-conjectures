/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode075
import Proofs.RadenkovicGutmanD37Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1369]],[[0,0],[0,0,0],[0,0]],[[0,0,12321],[0,24642,24642],[12321,24642]],[[0,0,0],[0,0,0],[0,0]],[[-110889,406593,217671],[406593,657120,65712],[217671,65712]],[[0,0,0],[0,0,0],[0,0]],[[1404594,6542451,954193],[6542451,3091202,60236],[954193,60236]],[[0,0,0],[0,0,0],[0,0]],[[39587373,37689939,1957670],[37689939,6576676,21904],[1957670,21904]],[[0,0,0],[0,0,0],[0,0]],[[305076174,116017274,2250636],[116017274,7786872,2738],[2250636,2738]],[[0,0,0],[0,0],[0]],[[1269390191,222165427,1555184],[222165427,5536236],[1555184]],[[0,0,0],[0,0],[0]],[[3403744700,285199663,658489],[285199663,2412178],[658489]],[[0,0,0],[0,0],[0]],[[6387329610,255428020,167018],[255428020,629740],[167018]],[[0,0,0],[0,0],[0]],[[8785445242,162816539,23273],[162816539,90354],[23273]],[[0,0,0],[0,0],[0]],[[9106820730,74277833,1369],[74277833,5476],[1369]],[[0,0],[0]],[[7233604340,24061544],[24061544]],[[0,0],[0]],[[4441761570,5400705],[5400705]],[[0,0],[0]],[[2113651122,798127],[798127]],[[0,0],[0]],[[776632331,69819],[69819]],[[0,0],[0]],[[218048844,2738],[2738]],[[0]],[[45875190]],[[0]],[[6995590]],[[0]],[[729677]],[[0]],[[46546]],[[0]],[[1369]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
