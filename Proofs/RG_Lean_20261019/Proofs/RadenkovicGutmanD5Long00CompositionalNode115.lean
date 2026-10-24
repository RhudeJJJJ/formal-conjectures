/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode113
import Proofs.RadenkovicGutmanD5Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,25]],[[0,0],[0,0,0],[0,0]],[[0,0,225],[0,0,450],[225,450]],[[0,0,0],[0,0,0],[0,0]],[[2025,4050,3975],[4050,8100,1200],[3975,1200]],[[0,0,0],[0,0,0],[0,0]],[[71550,82350,17425],[82350,43200,1100],[17425,1100]],[[0,0,0],[0,0,0],[0,0]],[[945675,514350,35750],[514350,97200,400],[35750,400]],[[0,0,0],[0,0,0],[0,0]],[[6184650,1658400,41100],[1658400,120000,50],[41100,50]],[[0,0,0],[0,0],[0]],[[24253525,3286550,28400],[3286550,88600],[28400]],[[0,0,0],[0,0],[0]],[[63416500,4343750,12025],[4343750,40000],[12025]],[[0,0,0],[0,0],[0]],[[117663550,3994900,3050],[3994900,10800],[3050]],[[0,0,0],[0,0],[0]],[[161014450,2610800,425],[2610800,1600],[425]],[[0,0,0],[0,0],[0]],[[166532800,1219750,25],[1219750,100],[25]],[[0,0],[0]],[[132158000,404250],[404250]],[[0,0],[0]],[[81124000,92750],[92750]],[[0,0],[0]],[[38599550,14000],[14000]],[[0,0],[0]],[[14182525,1250],[1250]],[[0,0],[0]],[[3981900,50],[50]],[[0]],[[837750]],[[0]],[[127750]],[[0]],[[13325]],[[0]],[[850]],[[0]],[[25]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
