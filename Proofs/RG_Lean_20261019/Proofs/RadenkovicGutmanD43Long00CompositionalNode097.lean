/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode051
import Proofs.RadenkovicGutmanD43Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5547],[0,-5547]],[[0,0,0],[0,0,0],[0,0]],[[0,49923,-83205],[49923,-249615,-24295],[-83205,-24295]],[[0,0,0],[0,0,0],[0,0]],[[748845,-1649781,-640227],[-1649781,-1839024,-30702],[-640227,-30702]],[[0,0,0],[0,0,0],[0,0]],[[-4278285,-20088396,-1961402],[-20088396,-5388975,-14319],[-1961402,-14319]],[[0,0,0],[0,0,0],[0,0]],[[-126254106,-94315469,-3138269],[-94315469,-8296076,-2451],[-3138269,-2451]],[[0,0,0],[0,0,0],[0,0]],[[-878198331,-248030880,-2882978],[-248030880,-7387744,-86],[-2882978,-86]],[[0,0,0],[0,0],[0]],[[-3325579279,-414651709,-1569027],[-414651709,-3926674],[-1569027]],[[0,0,0],[0,0],[0]],[[-8182133052,-467751334,-500778],[-467751334,-1232767],[-500778]],[[0,0,0],[0,0],[0]],[[-14136014704,-366744549,-87591],[-366744549,-213968],[-87591]],[[0,0,0],[0,0],[0]],[[-17886309455,-202159211,-6837],[-202159211,-16899],[-6837]],[[0,0,0],[0,0],[0]],[[-16984060450,-78081034,-86],[-78081034,-258],[-86]],[[0,0],[0]],[[-12268797324,-20714906],[-20714906]],[[0,0],[0]],[[-6781268732,-3610538],[-3610538]],[[0,0],[0]],[[-2864926385,-377024],[-377024]],[[0,0],[0]],[[-917589427,-18920],[-18920]],[[0,0],[0]],[[-219016200,-172],[-172]],[[0]],[[-37799580]],[[0]],[[-4476085]],[[0]],[[-329681]],[[0]],[[-12083]],[[0]],[[-86]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
