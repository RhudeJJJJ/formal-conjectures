/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode051
import Proofs.RadenkovicGutmanD33Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1089]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,26136],[0,26136,66]],[[0,0,0],[0,0,0],[0,0]],[[-88209,58806,147015],[58806,589248,81774],[147015,81774]],[[0,0,0],[0,0,0],[0,0]],[[-465102,3950694,887436],[3950694,3560040,85932],[887436,85932]],[[0,0,0],[0,0,0],[0,0]],[[21623679,32521500,2223936],[32521500,8930724,35574],[2223936,35574]],[[0,0,0],[0,0,0],[0,0]],[[258054390,124441020,3019698],[124441020,12139248,5412],[3019698,5412]],[[0,0,0],[0,0,0],[0,0]],[[1361284947,282086244,2429262],[282086244,9775656,132],[2429262,132]],[[0,0,0],[0,0],[0]],[[4350355086,418626186,1188858],[418626186,4788432],[1188858]],[[0,0,0],[0,0],[0]],[[9442935678,427469856,348744],[427469856,1405668],[348744]],[[0,0,0],[0,0],[0]],[[14755045008,307871850,57222],[307871850,230736],[57222]],[[0,0,0],[0,0],[0]],[[17161527108,157742970,4323],[157742970,17424],[4323]],[[0,0,0],[0,0],[0]],[[15155303592,57199692,66],[57199692,264],[66]],[[0,0],[0]],[[10273150140,14374800],[14374800]],[[0,0],[0]],[[5367010440,2394546],[2394546]],[[0,0],[0]],[[2156252307,241692],[241692]],[[0,0],[0]],[[660267102,12012],[12012]],[[0,0],[0]],[[151417926,132],[132]],[[0]],[[25233120]],[[0]],[[2901855]],[[0]],[[209418]],[[0]],[[7689]],[[0]],[[66]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
