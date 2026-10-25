/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode070
import Proofs.RadenkovicGutmanD13Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,312],[0,312,536]],[[0,0,0],[0,0,0],[0,0,0]],[[0,2808,8892],[2808,21816,11312],[8892,11312,4]],[[0,0,0],[0,0,0],[0,0]],[[-7128,301644,118608],[301644,354852,28816],[118608,28816]],[[0,0,0],[0,0,0],[0,0]],[[1808136,3909672,484960],[3909672,1531488,26168],[484960,26168]],[[0,0,0],[0,0,0],[0,0]],[[28731780,20799212,965344],[20799212,3149892,9584],[965344,9584]],[[0,0,0],[0,0,0],[0,0]],[[192123492,61487332,1092104],[61487332,3669832,1240],[1092104,1240]],[[0,0,0],[0,0,0],[0,0]],[[747883532,114971252,748016],[114971252,2590528,8],[748016,8]],[[0,0,0],[0,0],[0]],[[1928906616,145371200,315652],[145371200,1127840],[315652]],[[0,0,0],[0,0],[0]],[[3529028280,128916912,80288],[128916912,296196],[80288]],[[0,0,0],[0,0],[0]],[[4769017760,81670884,11348],[81670884,43248],[11348]],[[0,0,0],[0,0],[0]],[[4880873428,37144148,704],[37144148,2772],[704]],[[0,0,0],[0,0],[0]],[[3841017576,12032460,4],[12032460,16],[4]],[[0,0],[0]],[[2342882944,2711196],[2711196]],[[0,0],[0]],[[1109923032,404752],[404752]],[[0,0],[0]],[[406854708,36268],[36268]],[[0,0],[0]],[[114209448,1532],[1532]],[[0,0],[0]],[[24090184,8],[8]],[[0]],[[3697824]],[[0]],[[391044]],[[0]],[[25712]],[[0]],[[828]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
