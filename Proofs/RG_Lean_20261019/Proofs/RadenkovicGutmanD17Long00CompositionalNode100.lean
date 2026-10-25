/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode043
import Proofs.RadenkovicGutmanD17Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-2601],[0,-5202,1530],[-2601,1530]],[[0,0,0],[0,0,0],[0,0]],[[0,-103275,-8772],[-103275,5406,6630],[-8772,6630]],[[0,0,0],[0,0,0],[0,0]],[[-963900,-856035,19805],[-856035,192610,8160],[19805,8160]],[[0,0,0],[0,0,0],[0,0]],[[-11750400,-2721411,133858],[-2721411,665006,3570],[133858,3570]],[[0,0,0],[0,0,0],[0,0]],[[-63548550,-3607740,257754],[-3607740,1054068,510],[257754,510]],[[0,0,0],[0,0],[0]],[[-201262830,915977,252110],[915977,926500],[252110]],[[0,0,0],[0,0],[0]],[[-412663814,10797329,139281],[10797329,476442],[139281]],[[0,0,0],[0,0],[0]],[[-566134952,18429088,43894],[18429088,142358],[43894]],[[0,0,0],[0,0],[0]],[[-505226910,17584443,7361],[17584443,22882],[7361]],[[0,0,0],[0,0],[0]],[[-239184220,10836769,510],[10836769,1530],[510]],[[0,0],[0]],[[42963896,4476882],[4476882]],[[0,0],[0]],[[175698230,1234795],[1234795]],[[0,0],[0]],[[158137366,218501],[218501]],[[0,0],[0]],[[86852490,22457],[22457]],[[0,0],[0]],[[32848386,1020],[1020]],[[0]],[[8775060]],[[0]],[[1635230]],[[0]],[[202912]],[[0]],[[15096]],[[0]],[[510]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
