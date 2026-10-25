/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,147],[0,147]],[[0,0,0],[0,0,0],[0,0]],[[0,-1323,2205],[-1323,6615,679],[2205,679]],[[0,0,0],[0,0,0],[0,0]],[[-19845,44037,17283],[44037,49896,966],[17283,966]],[[0,0,0],[0,0,0],[0,0]],[[118125,544068,54194],[544068,150759,567],[54194,567]],[[0,0,0],[0,0,0],[0,0]],[[3461346,2594165,89285],[2594165,241220,147],[89285,147]],[[0,0,0],[0,0,0],[0,0]],[[24281859,6938232,85274],[6938232,225904,14],[85274,14]],[[0,0,0],[0,0],[0]],[[92898799,11820277,49035],[11820277,128674],[49035]],[[0,0,0],[0,0],[0]],[[231147924,13627390,17010],[13627390,44695],[17010]],[[0,0,0],[0,0],[0]],[[404263552,10965549,3423],[10965549,9128],[3423]],[[0,0,0],[0,0],[0]],[[518458871,6241739,357],[6241739,987],[357]],[[0,0,0],[0,0],[0]],[[499816618,2512930,14],[2512930,42],[14]],[[0,0],[0]],[[367385676,705530],[705530]],[[0,0],[0]],[[207264092,133658],[133658]],[[0,0],[0]],[[89764073,16016],[16016]],[[0,0],[0]],[[29657635,1064],[1064]],[[0,0],[0]],[[7371840,28],[28]],[[0]],[[1345260]],[[0]],[[173005]],[[0]],[[14609]],[[0]],[[707]],[[0]],[[14]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
