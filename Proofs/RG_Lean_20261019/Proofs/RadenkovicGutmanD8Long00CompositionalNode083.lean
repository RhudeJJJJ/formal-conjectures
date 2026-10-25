/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode070
import Proofs.RadenkovicGutmanD8Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,192],[0,192,176]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1728,4032],[1728,10656,4192],[4032,4192,4]],[[0,0,0],[0,0,0],[0,0]],[[9072,139104,48048],[139104,144552,10376],[48048,10376]],[[0,0,0],[0,0,0],[0,0]],[[966276,1661832,189700],[1661832,595808,9408],[189700,9408]],[[0,0,0],[0,0,0],[0,0]],[[13291560,8526232,371904],[8526232,1202792,3504],[371904,3504]],[[0,0,0],[0,0,0],[0,0]],[[84155052,24718872,417904],[24718872,1390672,480],[417904,480]],[[0,0,0],[0,0,0],[0,0]],[[318228472,45697312,285856],[45697312,980768,8],[285856,8]],[[0,0,0],[0,0],[0]],[[806314196,57398360,121112],[57398360,429200],[121112]],[[0,0,0],[0,0],[0]],[[1458065200,50731352,31168],[50731352,114216],[31168]],[[0,0,0],[0,0],[0]],[[1954868440,32118544,4528],[32118544,17168],[4528]],[[0,0,0],[0,0],[0]],[[1990168488,14637728,304],[14637728,1192],[304]],[[0,0,0],[0,0],[0]],[[1561064896,4767000,4],[4767000,16],[4]],[[0,0],[0]],[[950751104,1084936],[1084936]],[[0,0],[0]],[[450493152,164952],[164952]],[[0,0],[0]],[[165470728,15328],[15328]],[[0,0],[0]],[[46651508,712],[712]],[[0,0],[0]],[[9914384,8],[8]],[[0]],[[1540984]],[[0]],[[166504]],[[0]],[[11412]],[[0]],[[408]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
