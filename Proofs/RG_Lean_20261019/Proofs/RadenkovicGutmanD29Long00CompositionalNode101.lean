/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode051
import Proofs.RadenkovicGutmanD29Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,841]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,20184],[0,20184,58]],[[0,0,0],[0,0,0],[0,0]],[[-68121,45414,113535],[45414,455184,63278],[113535,63278]],[[0,0,0],[0,0,0],[0,0]],[[-358614,3052134,685908],[3052134,2752680,66700],[685908,66700]],[[0,0,0],[0,0,0],[0,0]],[[16719399,25138476,1720512],[25138476,6912788,27782],[1720512,27782]],[[0,0,0],[0,0,0],[0,0]],[[199553118,96246476,2338850],[96246476,9408528,4292],[2338850,4292]],[[0,0,0],[0,0,0],[0,0]],[[1053016187,218312580,1884478],[218312580,7589416,116],[1884478,116]],[[0,0,0],[0,0],[0]],[[3366460998,324215882,924346],[324215882,3726384],[924346]],[[0,0,0],[0,0],[0]],[[7310311822,331342864,272136],[331342864,1097940],[272136]],[[0,0,0],[0,0],[0]],[[11427939520,238883034,44950],[238883034,181424],[44950]],[[0,0,0],[0,0],[0]],[[13298579764,122554058,3451],[122554058,13920],[3451]],[[0,0,0],[0,0],[0]],[[11750789096,44516508,58],[44516508,232],[58]],[[0,0],[0]],[[7970790940,11214880],[11214880]],[[0,0],[0]],[[4167584200,1875314],[1875314]],[[0,0],[0]],[[1676059611,190588],[190588]],[[0,0],[0]],[[513891542,9628],[9628]],[[0,0],[0]],[[118054998,116],[116]],[[0]],[[19722320]],[[0]],[[2276935]],[[0]],[[165474]],[[0]],[[6177]],[[0]],[[58]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
