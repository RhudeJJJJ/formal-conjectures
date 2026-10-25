/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode113
import Proofs.RadenkovicGutmanD35Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1225]],[[0,0],[0,0,0],[0,0]],[[0,0,11025],[0,0,22050],[11025,22050]],[[0,0,0],[0,0,0],[0,0]],[[99225,198450,194775],[198450,396900,58800],[194775,58800]],[[0,0,0],[0,0,0],[0,0]],[[3505950,4035150,853825],[4035150,2116800,53900],[853825,53900]],[[0,0,0],[0,0,0],[0,0]],[[46338075,25203150,1751750],[25203150,4762800,19600],[1751750,19600]],[[0,0,0],[0,0,0],[0,0]],[[303047850,81261600,2013900],[81261600,5880000,2450],[2013900,2450]],[[0,0,0],[0,0],[0]],[[1188422725,161040950,1391600],[161040950,4341400],[1391600]],[[0,0,0],[0,0],[0]],[[3107408500,212843750,589225],[212843750,1960000],[589225]],[[0,0,0],[0,0],[0]],[[5765513950,195750100,149450],[195750100,529200],[149450]],[[0,0,0],[0,0],[0]],[[7889708050,127929200,20825],[127929200,78400],[20825]],[[0,0,0],[0,0],[0]],[[8160107200,59767750,1225],[59767750,4900],[1225]],[[0,0],[0]],[[6475742000,19808250],[19808250]],[[0,0],[0]],[[3975076000,4544750],[4544750]],[[0,0],[0]],[[1891377950,686000],[686000]],[[0,0],[0]],[[694943725,61250],[61250]],[[0,0],[0]],[[195113100,2450],[2450]],[[0]],[[41049750]],[[0]],[[6259750]],[[0]],[[652925]],[[0]],[[41650]],[[0]],[[1225]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
