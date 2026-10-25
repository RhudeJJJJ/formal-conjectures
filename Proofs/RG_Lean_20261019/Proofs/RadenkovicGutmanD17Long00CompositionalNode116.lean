/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode115
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e116 : NestedArithmetic.Expr 3 := .scaled (-1) e115
noncomputable def p116 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-289]],[[0,0],[0,0,0],[0,0]],[[0,0,-2601],[0,0,-5202],[-2601,-5202]],[[0,0,0],[0,0,0],[0,0]],[[-23409,-46818,-45951],[-46818,-93636,-13872],[-45951,-13872]],[[0,0,0],[0,0,0],[0,0]],[[-827118,-951966,-201433],[-951966,-499392,-12716],[-201433,-12716]],[[0,0,0],[0,0,0],[0,0]],[[-10932003,-5945886,-413270],[-5945886,-1123632,-4624],[-413270,-4624]],[[0,0,0],[0,0,0],[0,0]],[[-71494554,-19171104,-475116],[-19171104,-1387200,-578],[-475116,-578]],[[0,0,0],[0,0],[0]],[[-280370749,-37992518,-328304],[-37992518,-1024216],[-328304]],[[0,0,0],[0,0],[0]],[[-733094740,-50213750,-139009],[-50213750,-462400],[-139009]],[[0,0,0],[0,0],[0]],[[-1360190638,-46181044,-35258],[-46181044,-124848],[-35258]],[[0,0,0],[0,0],[0]],[[-1861327042,-30180848,-4913],[-30180848,-18496],[-4913]],[[0,0,0],[0,0],[0]],[[-1925119168,-14100310,-289],[-14100310,-1156],[-289]],[[0,0],[0]],[[-1527746480,-4673130],[-4673130]],[[0,0],[0]],[[-937793440,-1072190],[-1072190]],[[0,0],[0]],[[-446210798,-161840],[-161840]],[[0,0],[0]],[[-163949989,-14450],[-14450]],[[0,0],[0]],[[-46030764,-578],[-578]],[[0]],[[-9684390]],[[0]],[[-1476790]],[[0]],[[-154037]],[[0]],[[-9826]],[[0]],[[-289]]]
theorem step116 : p116=NestedHorner.scale (-1) p115 := by decide +kernel
#print axioms step116
theorem h116 : NestedArithmetic.compile e116=p116 := StagedExprCompile.compile_scaled (-1) e116 e115 p115 p116 rfl h115 step116
#print axioms h116
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
