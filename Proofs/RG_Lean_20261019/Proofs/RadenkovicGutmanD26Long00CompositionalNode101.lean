/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode051
import Proofs.RadenkovicGutmanD26Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,676]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,16224],[0,16224,52]],[[0,0,0],[0,0,0],[0,0]],[[-54756,36504,91260],[36504,365976,50960],[91260,50960]],[[0,0,0],[0,0,0],[0,0]],[[-287820,2454192,551772],[2454192,2215200,53872],[551772,53872]],[[0,0,0],[0,0,0],[0,0]],[[13454532,20224152,1385280],[20224152,5568680,22568],[1385280,22568]],[[0,0,0],[0,0,0],[0,0]],[[160605276,77474072,1885208],[77474072,7588464,3536],[1885208,3536]],[[0,0,0],[0,0,0],[0,0]],[[847750436,175837584,1521208],[175837584,6131008,104],[1521208,104]],[[0,0,0],[0,0],[0]],[[2711196852,261313520,747760],[261313520,3017040],[747760]],[[0,0,0],[0,0],[0]],[[5889710632,267269704,220896],[267269704,892008],[220896]],[[0,0,0],[0,0],[0]],[[9211152808,192874968,36712],[192874968,148304],[36712]],[[0,0,0],[0,0],[0]],[[10724110696,99071336,2860],[99071336,11544],[2860]],[[0,0,0],[0,0],[0]],[[9481176224,36045048,52],[36045048,208],[52]],[[0,0],[0]],[[6435398320,9101560],[9101560]],[[0,0],[0]],[[3367380640,1527344],[1527344]],[[0,0],[0]],[[1355530644,156208],[156208]],[[0,0],[0]],[[416120276,8008],[8008]],[[0,0],[0]],[[95749992,104],[104]],[[0]],[[16033160]],[[0]],[[1857700]],[[0]],[[135876]],[[0]],[[5148]],[[0]],[[52]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
