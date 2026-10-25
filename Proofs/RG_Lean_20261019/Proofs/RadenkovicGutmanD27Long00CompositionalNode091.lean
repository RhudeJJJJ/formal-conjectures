/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2187],[0,2187]],[[0,0,0],[0,0,0],[0,0]],[[0,19683,32805],[19683,104976,9639],[32805,9639]],[[0,0,0],[0,0,0],[0,0]],[[354294,1221804,252963],[1221804,784404,12366],[252963,12366]],[[0,0,0],[0,0,0],[0,0]],[[12308436,11461338,777114],[11461338,2335716,5967],[777114,5967]],[[0,0,0],[0,0,0],[0,0]],[[127169676,49582692,1247805],[49582692,3655692,1107],[1247805,1107]],[[0,0,0],[0,0,0],[0,0]],[[680256144,125216010,1151874],[125216010,3312792,54],[1151874,54]],[[0,0,0],[0,0],[0]],[[2269618542,204221250,631395],[204221250,1796580],[631395]],[[0,0,0],[0,0],[0]],[[5172497676,226556028,203850],[226556028,579204],[203850]],[[0,0,0],[0,0],[0]],[[8480766528,175610241,36423],[175610241,104868],[36423]],[[0,0,0],[0,0],[0]],[[10325977578,96123753,2997],[96123753,9072],[2997]],[[0,0,0],[0,0],[0]],[[9521060706,37039761,54],[37039761,216],[54]],[[0,0],[0]],[[6722907066,9863424],[9863424]],[[0,0],[0]],[[3652021080,1742391],[1742391]],[[0,0],[0]],[[1523927412,188082],[188082]],[[0,0],[0]],[[484582122,10341],[10341]],[[0,0],[0]],[[115536240,162],[162]],[[0]],[[20086704]],[[0]],[[2429298]],[[0]],[[187920]],[[0]],[[7830]],[[0]],[[108]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
