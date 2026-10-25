/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode033
import Proofs.RadenkovicGutmanD24Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,576]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,10368],[0,10368]],[[0,0,0],[0,0,0],[0,0]],[[-46656,0,46656],[0,186624,27648],[46656,27648]],[[0,0,0],[0,0,0],[0,0]],[[-808704,839808,248832],[839808,995328,25344],[248832,25344]],[[0,0,0],[0,0,0],[0,0]],[[-2472768,6718464,559872],[6718464,2239488,9216],[559872,9216]],[[0,0,0],[0,0,0],[0,0]],[[11750400,24074496,691200],[24074496,2764800,1152],[691200,1152]],[[0,0,0],[0,0],[0]],[[111987648,51010560,510336],[51010560,2041344],[510336]],[[0,0,0],[0,0],[0]],[[413397504,71072640,230400],[71072640,921600],[230400]],[[0,0,0],[0,0],[0]],[[944394624,68511744,62208],[68511744,248832],[62208]],[[0,0,0],[0,0],[0]],[[1503942912,46812672,9216],[46812672,36864],[9216]],[[0,0,0],[0,0],[0]],[[1759226112,22837248,576],[22837248,2304],[576]],[[0,0],[0]],[[1552972032,7896960],[7896960]],[[0,0],[0]],[[1048983552,1889280],[1889280]],[[0,0],[0]],[[544965120,297216],[297216]],[[0,0],[0]],[[217308096,27648],[27648]],[[0,0],[0]],[[65885184,1152],[1152]],[[0]],[[14905728]],[[0]],[[2435328]],[[0]],[[271296]],[[0]],[[18432]],[[0]],[[576]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
