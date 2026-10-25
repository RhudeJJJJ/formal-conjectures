/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,36]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-648,648],[0,648]],[[0,0,0],[0,0,0],[0,0]],[[2916,-5832,2916],[-5832,6048,1728],[2916,1728]],[[0,0,0],[0,0,0],[0,0]],[[-1944,-13608,15552],[-13608,43128,1584],[15552,1584]],[[0,0,0],[0,0,0],[0,0]],[[-107892,99144,34992],[99144,106992,576],[34992,576]],[[0,0,0],[0,0,0],[0,0]],[[-297000,621216,43200],[621216,140832,72],[43200,72]],[[0,0,0],[0,0],[0]],[[625140,1643688,31896],[1643688,109584],[31896]],[[0,0,0],[0,0],[0]],[[5931504,2629080,14400],[2629080,51768],[14400]],[[0,0,0],[0,0],[0]],[[18531864,2811312,3888],[2811312,14544],[3888]],[[0,0,0],[0,0],[0]],[[35633304,2092032,576],[2092032,2232],[576]],[[0,0,0],[0,0],[0]],[[47958624,1098216,36],[1098216,144],[36]],[[0,0],[0]],[[47557152,405000],[405000]],[[0,0],[0]],[[35584992,102600],[102600]],[[0,0],[0]],[[20291400,16992],[16992]],[[0,0],[0]],[[8821332,1656],[1656]],[[0,0],[0]],[[2900304,72],[72]],[[0]],[[708408]],[[0]],[[124488]],[[0]],[[14868]],[[0]],[[1080]],[[0]],[[36]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
