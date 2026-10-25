/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode095
import Proofs.RadenkovicGutmanD22Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1584,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14256,-14256,0],[-14256,-13728,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-375408,-161568,0],[-161568,-46640,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3706560,-784080,0],[-784080,-80608,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19974768,-2159520,0],[-2159520,-78144,0],[0,0]],[[0,0,0],[0,0],[0]],[[-68263184,-3775376,0],[-3775376,-44000],[0]],[[0,0,0],[0,0],[0]],[[-160068128,-4431680,0],[-4431680,-14256],[0]],[[0,0,0],[0,0],[0]],[[-269893184,-3594976,0],[-3594976,-2464],[0]],[[0,0,0],[0,0],[0]],[[-337001808,-2038080,0],[-2038080,-176],[0]],[[0,0,0],[0,0],[0]],[[-317424800,-804496,0],[-804496,0],[0]],[[0,0],[0]],[[-227936544,-216480],[-216480]],[[0,0],[0]],[[-125295104,-37840],[-37840]],[[0,0],[0]],[[-52611856,-3872],[-3872]],[[0,0],[0]],[[-16722640,-176],[-176]],[[0,0],[0]],[[-3950496,0],[0]],[[0]],[[-671616]],[[0]],[[-77616]],[[0]],[[-5456]],[[0]],[[-176]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
