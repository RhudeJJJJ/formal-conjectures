/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,121]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2178,2178],[0,2178]],[[0,0,0],[0,0,0],[0,0]],[[9801,-19602,9801],[-19602,20328,5808],[9801,5808]],[[0,0,0],[0,0,0],[0,0]],[[-6534,-45738,52272],[-45738,144958,5324],[52272,5324]],[[0,0,0],[0,0,0],[0,0]],[[-362637,333234,117612],[333234,359612,1936],[117612,1936]],[[0,0,0],[0,0,0],[0,0]],[[-998250,2087976,145200],[2087976,473352,242],[145200,242]],[[0,0,0],[0,0],[0]],[[2101165,5524618,107206],[5524618,368324],[107206]],[[0,0,0],[0,0],[0]],[[19936444,8836630,48400],[8836630,173998],[48400]],[[0,0,0],[0,0],[0]],[[62287654,9449132,13068],[9449132,48884],[13068]],[[0,0,0],[0,0],[0]],[[119767494,7031552,1936],[7031552,7502],[1936]],[[0,0,0],[0,0],[0]],[[161194264,3691226,121],[3691226,484],[121]],[[0,0],[0]],[[159844872,1361250],[1361250]],[[0,0],[0]],[[119605112,344850],[344850]],[[0,0],[0]],[[68201650,57112],[57112]],[[0,0],[0]],[[29649477,5566],[5566]],[[0,0],[0]],[[9748244,242],[242]],[[0]],[[2381038]],[[0]],[[418418]],[[0]],[[49973]],[[0]],[[3630]],[[0]],[[121]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
