/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode033
import Proofs.RadenkovicGutmanD11Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,121]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,2178],[0,2178]],[[0,0,0],[0,0,0],[0,0]],[[-9801,0,9801],[0,39204,5808],[9801,5808]],[[0,0,0],[0,0,0],[0,0]],[[-169884,176418,52272],[176418,209088,5324],[52272,5324]],[[0,0,0],[0,0,0],[0,0]],[[-519453,1411344,117612],[1411344,470448,1936],[117612,1936]],[[0,0,0],[0,0,0],[0,0]],[[2468400,5057316,145200],[5057316,580800,242],[145200,242]],[[0,0,0],[0,0],[0]],[[23525183,10715760,107206],[10715760,428824],[107206]],[[0,0,0],[0,0],[0]],[[86842184,14930190,48400],[14930190,193600],[48400]],[[0,0,0],[0,0],[0]],[[198388454,14392224,13068],[14392224,52272],[13068]],[[0,0,0],[0,0],[0]],[[315932452,9833912,1936],[9833912,7744],[1936]],[[0,0,0],[0,0],[0]],[[369559652,4797408,121],[4797408,484],[121]],[[0,0],[0]],[[326231972,1658910],[1658910]],[[0,0],[0]],[[220359392,396880],[396880]],[[0,0],[0]],[[114480520,62436],[62436]],[[0,0],[0]],[[45649791,5808],[5808]],[[0,0],[0]],[[13840464,242],[242]],[[0]],[[3131238]],[[0]],[[511588]],[[0]],[[56991]],[[0]],[[3872]],[[0]],[[121]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
