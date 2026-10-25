/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode051
import Proofs.RadenkovicGutmanD41Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1681]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,40344],[0,40344,82]],[[0,0,0],[0,0,0],[0,0]],[[-136161,90774,226935],[90774,909216,125870],[226935,125870]],[[0,0,0],[0,0,0],[0,0]],[[-719550,6095142,1368252],[6095142,5485800,131692],[1368252,131692]],[[0,0,0],[0,0,0],[0,0]],[[33321807,50135292,3424320],[50135292,13740740,54038],[3424320,54038]],[[0,0,0],[0,0,0],[0,0]],[[397585446,191680412,4641938],[191680412,18642864,8036],[4641938,8036]],[[0,0,0],[0,0,0],[0,0]],[[2096386211,434114724,3725998],[434114724,14976808,164],[3725998,164]],[[0,0,0],[0,0],[0]],[[6696001182,643585610,1817530],[643585610,7311120],[1817530]],[[0,0,0],[0,0],[0]],[[14525859742,656396224,530376],[656396224,2134788],[530376]],[[0,0,0],[0,0],[0]],[[22682592688,472059978,86182],[472059978,347024],[86182]],[[0,0,0],[0,0],[0]],[[26362811236,241418906,6355],[241418906,25584],[6355]],[[0,0,0],[0,0],[0]],[[23261580584,87324588,82],[87324588,328],[82]],[[0,0],[0]],[[15752733820,21867760],[21867760]],[[0,0],[0]],[[8220108040,3622514],[3622514]],[[0,0],[0]],[[3297737379,361948],[361948]],[[0,0],[0]],[[1007922926,17548],[17548]],[[0,0],[0]],[[230565222,164],[164]],[[0]],[[38284160]],[[0]],[[4377775]],[[0]],[[312666]],[[0]],[[11193]],[[0]],[[82]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
