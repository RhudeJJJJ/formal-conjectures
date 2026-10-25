/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,256]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-4608,4608],[0,4608]],[[0,0,0],[0,0,0],[0,0]],[[20736,-41472,20736],[-41472,43008,12288],[20736,12288]],[[0,0,0],[0,0,0],[0,0]],[[-13824,-96768,110592],[-96768,306688,11264],[110592,11264]],[[0,0,0],[0,0,0],[0,0]],[[-767232,705024,248832],[705024,760832,4096],[248832,4096]],[[0,0,0],[0,0,0],[0,0]],[[-2112000,4417536,307200],[4417536,1001472,512],[307200,512]],[[0,0,0],[0,0],[0]],[[4445440,11688448,226816],[11688448,779264],[226816]],[[0,0,0],[0,0],[0]],[[42179584,18695680,102400],[18695680,368128],[102400]],[[0,0,0],[0,0],[0]],[[131782144,19991552,27648],[19991552,103424],[27648]],[[0,0,0],[0,0],[0]],[[253392384,14876672,4096],[14876672,15872],[4096]],[[0,0,0],[0,0],[0]],[[341039104,7809536,256],[7809536,1024],[256]],[[0,0],[0]],[[338184192,2880000],[2880000]],[[0,0],[0]],[[253048832,729600],[729600]],[[0,0],[0]],[[144294400,120832],[120832]],[[0,0],[0]],[[62729472,11776],[11776]],[[0,0],[0]],[[20624384,512],[512]],[[0]],[[5037568]],[[0]],[[885248]],[[0]],[[105728]],[[0]],[[7680]],[[0]],[[256]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
