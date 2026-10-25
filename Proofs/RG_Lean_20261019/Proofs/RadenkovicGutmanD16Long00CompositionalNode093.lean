/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode033
import Proofs.RadenkovicGutmanD16Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,256]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,6144],[0,6144,32]],[[0,0,0],[0,0,0],[0,0]],[[-20736,-13824,34560],[-13824,133632,19520],[34560,19520]],[[0,0,0],[0,0,0],[0,0]],[[-569376,525312,209952],[525312,799872,20992],[209952,20992]],[[0,0,0],[0,0,0],[0,0]],[[-2457216,5170752,529920],[5170752,1984000,9088],[529920,9088]],[[0,0,0],[0,0,0],[0,0]],[[5803872,20749312,725888],[20749312,2669056,1536],[725888,1536]],[[0,0,0],[0,0,0],[0,0]],[[84249344,47967360,590848],[47967360,2136064,64],[590848,64]],[[0,0,0],[0,0],[0]],[[350736608,72059392,294080],[72059392,1048320],[294080]],[[0,0,0],[0,0],[0]],[[868256512,74443712,88576],[74443712,312832],[88576]],[[0,0,0],[0,0],[0]],[[1476259520,54373888,15232],[54373888,53760],[15232]],[[0,0,0],[0,0],[0]],[[1830179456,28370176,1280],[28370176,4608],[1280]],[[0,0,0],[0,0],[0]],[[1705602176,10538496,32],[10538496,128],[32]],[[0,0],[0]],[[1214120064,2737600],[2737600]],[[0,0],[0]],[[664736768,478720],[478720]],[[0,0],[0]],[[279886336,52352],[52352]],[[0,0],[0]],[[90001632,3072],[3072]],[[0,0],[0]],[[21777408,64],[64]],[[0]],[[3864256]],[[0]],[[481664]],[[0]],[[39136]],[[0]],[[1792]],[[0]],[[32]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
