/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode113
import Proofs.RadenkovicGutmanD25Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,625]],[[0,0],[0,0,0],[0,0]],[[0,0,5625],[0,0,11250],[5625,11250]],[[0,0,0],[0,0,0],[0,0]],[[50625,101250,99375],[101250,202500,30000],[99375,30000]],[[0,0,0],[0,0,0],[0,0]],[[1788750,2058750,435625],[2058750,1080000,27500],[435625,27500]],[[0,0,0],[0,0,0],[0,0]],[[23641875,12858750,893750],[12858750,2430000,10000],[893750,10000]],[[0,0,0],[0,0,0],[0,0]],[[154616250,41460000,1027500],[41460000,3000000,1250],[1027500,1250]],[[0,0,0],[0,0],[0]],[[606338125,82163750,710000],[82163750,2215000],[710000]],[[0,0,0],[0,0],[0]],[[1585412500,108593750,300625],[108593750,1000000],[300625]],[[0,0,0],[0,0],[0]],[[2941588750,99872500,76250],[99872500,270000],[76250]],[[0,0,0],[0,0],[0]],[[4025361250,65270000,10625],[65270000,40000],[10625]],[[0,0,0],[0,0],[0]],[[4163320000,30493750,625],[30493750,2500],[625]],[[0,0],[0]],[[3303950000,10106250],[10106250]],[[0,0],[0]],[[2028100000,2318750],[2318750]],[[0,0],[0]],[[964988750,350000],[350000]],[[0,0],[0]],[[354563125,31250],[31250]],[[0,0],[0]],[[99547500,1250],[1250]],[[0]],[[20943750]],[[0]],[[3193750]],[[0]],[[333125]],[[0]],[[21250]],[[0]],[[625]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
