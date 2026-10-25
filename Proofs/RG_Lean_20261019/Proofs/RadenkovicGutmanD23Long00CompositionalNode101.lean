/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode051
import Proofs.RadenkovicGutmanD23Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,529]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,12696],[0,12696,46]],[[0,0,0],[0,0,0],[0,0]],[[-42849,28566,71415],[28566,286488,39974],[71415,39974]],[[0,0,0],[0,0,0],[0,0]],[[-224802,1921374,432216],[1921374,1736040,42412],[432216,42412]],[[0,0,0],[0,0,0],[0,0]],[[10543959,15843780,1086336],[15843780,4369724,17894],[1086336,17894]],[[0,0,0],[0,0,0],[0,0]],[[125881530,60736100,1480418],[60736100,5963808,2852],[1480418,2852]],[[0,0,0],[0,0,0],[0,0]],[[664715387,137952804,1196782],[137952804,4827976,92],[1196782,92]],[[0,0,0],[0,0],[0]],[[2126781066,205187186,589858],[205187186,2382432],[589858]],[[0,0,0],[0,0],[0]],[[4622423758,210072616,174984],[210072616,707388],[174984]],[[0,0,0],[0,0],[0]],[[7233116728,151781370,29302],[151781370,118496],[29302]],[[0,0,0],[0,0],[0]],[[8426277148,78082010,2323],[78082010,9384],[2323]],[[0,0,0],[0,0],[0]],[[7454797352,28465812,46],[28465812,184],[46]],[[0,0],[0]],[[5064042940,7208200],[7208200]],[[0,0],[0]],[[2652348040,1214906],[1214906]],[[0,0],[0]],[[1068957867,125212],[125212]],[[0,0],[0]],[[328643642,6532],[6532]],[[0,0],[0]],[[75774006,92],[92]],[[0]],[[12724520]],[[0]],[[1480855]],[[0]],[[109158]],[[0]],[[4209]],[[0]],[[46]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
