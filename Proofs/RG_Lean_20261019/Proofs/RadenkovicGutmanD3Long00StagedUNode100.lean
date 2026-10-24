/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode098
import Proofs.RadenkovicGutmanD3Long00StagedUNode099
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .plus e098 e099
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,9]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-81],[0,-162,234],[-81,234,6]],[[0,0,0],[0,0,0],[0,0]],[[-729,-2997,675],[-2997,4158,852],[675,852]],[[0,0,0],[0,0,0],[0,0]],[[-37422,-2997,6525],[-2997,31338,1068],[6525,1068]],[[0,0,0],[0,0,0],[0,0]],[[-269001,122121,19746],[122121,88818,576],[19746,576]],[[0,0,0],[0,0,0],[0,0]],[[-490644,720384,30804],[720384,133956,138],[30804,138]],[[0,0,0],[0,0,0],[0,0]],[[2311677,2020437,28188],[2020437,119916,12],[28188,12]],[[0,0,0],[0,0],[0]],[[16324596,3474627,15843],[3474627,66330],[15843]],[[0,0,0],[0,0],[0]],[[49249542,4003464,5502],[4003464,22746],[5502]],[[0,0,0],[0,0],[0]],[[94397370,3217989,1143],[3217989,4674],[1143]],[[0,0,0],[0,0],[0]],[[127587384,1836651,129],[1836651,522],[129]],[[0,0,0],[0,0],[0]],[[127298112,746262,6],[746262,24],[6]],[[0,0],[0]],[[95975490,213435],[213435]],[[0,0],[0]],[[55309902,41751],[41751]],[[0,0],[0]],[[24443733,5277],[5277]],[[0,0],[0]],[[8252268,384],[384]],[[0,0],[0]],[[2103786,12],[12]],[[0]],[[396390]],[[0]],[[53223]],[[0]],[[4782]],[[0]],[[255]],[[0]],[[6]]]
theorem step100 : p100=NestedHorner.add p098 p099 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_plus e100 e098 e099 p098 p099 p100 rfl h098 h099 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
