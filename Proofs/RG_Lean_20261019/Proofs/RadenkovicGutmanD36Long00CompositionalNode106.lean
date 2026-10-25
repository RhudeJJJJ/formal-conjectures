/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode095
import Proofs.RadenkovicGutmanD36Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2592,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23328,-23328,0],[-23328,-22464,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-614304,-264384,0],[-264384,-76320,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6065280,-1283040,0],[-1283040,-131904,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-32685984,-3533760,0],[-3533760,-127872,0],[0,0]],[[0,0,0],[0,0],[0]],[[-111703392,-6177888,0],[-6177888,-72000],[0]],[[0,0,0],[0,0],[0]],[[-261929664,-7251840,0],[-7251840,-23328],[0]],[[0,0,0],[0,0],[0]],[[-441643392,-5882688,0],[-5882688,-4032],[0]],[[0,0,0],[0,0],[0]],[[-551457504,-3335040,0],[-3335040,-288],[0]],[[0,0,0],[0,0],[0]],[[-519422400,-1316448,0],[-1316448,0],[0]],[[0,0],[0]],[[-372987072,-354240],[-354240]],[[0,0],[0]],[[-205028352,-61920],[-61920]],[[0,0],[0]],[[-86092128,-6336],[-6336]],[[0,0],[0]],[[-27364320,-288],[-288]],[[0,0],[0]],[[-6464448,0],[0]],[[0]],[[-1099008]],[[0]],[[-127008]],[[0]],[[-8928]],[[0]],[[-288]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
