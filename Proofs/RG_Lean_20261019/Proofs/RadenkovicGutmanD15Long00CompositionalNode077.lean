/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,2025],[0,4050],[2025]],[[0,0,0],[0,0],[0]],[[0,66825,17550],[66825,35100],[17550]],[[0,0,0],[0,0],[0]],[[546750,747225,59625],[747225,119250],[59625]],[[0,0,0],[0,0],[0]],[[7472250,3570075,103050],[3570075,206100],[103050]],[[0,0,0],[0,0],[0]],[[45550350,9663750,99900],[9663750,199800],[99900]],[[0,0,0],[0,0],[0]],[[164883600,16587675,56250],[16587675,112500],[56250]],[[0,0,0],[0,0],[0]],[[397934100,19110825,18225],[19110825,36450],[18225]],[[0,0,0],[0,0],[0]],[[680876100,15218100,3150],[15218100,6300],[3150]],[[0,0,0],[0,0],[0]],[[856441350,8473275,225],[8473275,450],[225]],[[0,0],[0]],[[809540550,3287025],[3287025]],[[0,0],[0]],[[582238800,869850],[869850]],[[0,0],[0]],[[320260050,149625],[149625]],[[0,0],[0]],[[134509050,15075],[15075]],[[0,0],[0]],[[42756300,675],[675]],[[0]],[[10100700]],[[0]],[[1717200]],[[0]],[[198450]],[[0]],[[13950]],[[0]],[[450]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
