/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode095
import Proofs.RadenkovicGutmanD26Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1872,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16848,-16848,0],[-16848,-16224,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-443664,-190944,0],[-190944,-55120,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4380480,-926640,0],[-926640,-95264,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23606544,-2552160,0],[-2552160,-92352,0],[0,0]],[[0,0,0],[0,0],[0]],[[-80674672,-4461808,0],[-4461808,-52000],[0]],[[0,0,0],[0,0],[0]],[[-189171424,-5237440,0],[-5237440,-16848],[0]],[[0,0,0],[0,0],[0]],[[-318964672,-4248608,0],[-4248608,-2912],[0]],[[0,0,0],[0,0],[0]],[[-398274864,-2408640,0],[-2408640,-208],[0]],[[0,0,0],[0,0],[0]],[[-375138400,-950768,0],[-950768,0],[0]],[[0,0],[0]],[[-269379552,-255840],[-255840]],[[0,0],[0]],[[-148076032,-44720],[-44720]],[[0,0],[0]],[[-62177648,-4576],[-4576]],[[0,0],[0]],[[-19763120,-208],[-208]],[[0,0],[0]],[[-4668768,0],[0]],[[0]],[[-793728]],[[0]],[[-91728]],[[0]],[[-6448]],[[0]],[[-208]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
