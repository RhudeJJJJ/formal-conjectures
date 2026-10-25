/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode035
import Proofs.RadenkovicGutmanD35Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-11025],[0,-22050,6930],[-11025,6930]],[[0,0,0],[0,0,0],[0,0]],[[0,-301455,-33180],[-301455,58380,30030],[-33180,30030]],[[0,0,0],[0,0,0],[0,0]],[[-1854090,-1573425,111965],[-1573425,1097110,36960],[111965,36960]],[[0,0,0],[0,0,0],[0,0]],[[-12989970,1352925,644770],[1352925,3701180,16170],[644770,16170]],[[0,0,0],[0,0,0],[0,0]],[[-512190,29654590,1204770],[29654590,5906880,2310],[1204770,2310]],[[0,0,0],[0,0],[0]],[[304211880,101941385,1162910],[101941385,5264140],[1162910]],[[0,0,0],[0,0],[0]],[[1550624880,188231855,637665],[188231855,2749110],[637665]],[[0,0,0],[0,0],[0]],[[4236968540,220980200,199990],[220980200,834260],[199990]],[[0,0,0],[0,0],[0]],[[7641266010,175343595,33425],[175343595,136150],[33425]],[[0,0,0],[0,0],[0]],[[9815665790,96303445,2310],[96303445,9240],[2310]],[[0,0],[0]],[[9323515740,36680140],[36680140]],[[0,0],[0]],[[6678654290,9511075],[9511075]],[[0,0],[0]],[[3640040950,1601915],[1601915]],[[0,0],[0]],[[1510323220,158025],[158025]],[[0,0],[0]],[[473466000,6930],[6930]],[[0]],[[110207160]],[[0]],[[18452910]],[[0]],[[2100070]],[[0]],[[145390]],[[0]],[[4620]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
