/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode051
import Proofs.RadenkovicGutmanD16Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,256]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,6144],[0,6144,32]],[[0,0,0],[0,0,0],[0,0]],[[-20736,13824,34560],[13824,138816,19520],[34560,19520]],[[0,0,0],[0,0,0],[0,0]],[[-108000,931392,209952],[931392,844800,20992],[209952,20992]],[[0,0,0],[0,0,0],[0,0]],[[5130432,7699392,529920],[7699392,2136640,9088],[529920,9088]],[[0,0,0],[0,0,0],[0,0]],[[61286496,29592512,725888],[29592512,2932864,1536],[725888,1536]],[[0,0,0],[0,0,0],[0,0]],[[324086336,67405824,590848],[67405824,2391808,64],[590848,64]],[[0,0,0],[0,0],[0]],[[1038665632,100576960,294080],[100576960,1192320],[294080]],[[0,0,0],[0,0],[0]],[[2261643392,103353024,88576],[103353024,359488],[88576]],[[0,0,0],[0,0],[0]],[[3546173888,75008128,15232],[75008128,61824],[15232]],[[0,0,0],[0,0],[0]],[[4140470336,38803456,1280],[38803456,5184],[1280]],[[0,0,0],[0,0],[0]],[[3672489984,14250688,32],[14250688,128],[32]],[[0,0],[0]],[[2502136320,3645760],[3645760]],[[0,0],[0]],[[1315159040,624064],[624064]],[[0,0],[0]],[[532339904,66048],[66048]],[[0,0],[0]],[[164566176,3648],[3648]],[[0,0],[0]],[[38220672,64],[64]],[[0]],[[6484160]],[[0]],[[766400]],[[0]],[[58016]],[[0]],[[2368]],[[0]],[[32]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
