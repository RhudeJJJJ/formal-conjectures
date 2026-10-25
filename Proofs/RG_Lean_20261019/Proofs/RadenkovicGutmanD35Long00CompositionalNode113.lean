/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1225]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-22050,22050],[0,22050]],[[0,0,0],[0,0,0],[0,0]],[[99225,-198450,99225],[-198450,205800,58800],[99225,58800]],[[0,0,0],[0,0,0],[0,0]],[[-66150,-463050,529200],[-463050,1467550,53900],[529200,53900]],[[0,0,0],[0,0,0],[0,0]],[[-3671325,3373650,1190700],[3373650,3640700,19600],[1190700,19600]],[[0,0,0],[0,0,0],[0,0]],[[-10106250,21138600,1470000],[21138600,4792200,2450],[1470000,2450]],[[0,0,0],[0,0],[0]],[[21272125,55931050,1085350],[55931050,3728900],[1085350]],[[0,0,0],[0,0],[0]],[[201835900,89461750,490000],[89461750,1761550],[490000]],[[0,0,0],[0,0],[0]],[[630598150,95662700,132300],[95662700,494900],[132300]],[[0,0,0],[0,0],[0]],[[1212522150,71187200,19600],[71187200,75950],[19600]],[[0,0,0],[0,0],[0]],[[1631925400,37369850,1225],[37369850,4900],[1225]],[[0,0],[0]],[[1618264200,13781250],[13781250]],[[0,0],[0]],[[1210878200,3491250],[3491250]],[[0,0],[0]],[[690471250,578200],[578200]],[[0,0],[0]],[[300170325,56350],[56350]],[[0,0],[0]],[[98690900,2450],[2450]],[[0]],[[24105550]],[[0]],[[4236050]],[[0]],[[505925]],[[0]],[[36750]],[[0]],[[1225]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
