/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1024]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-18432,18432],[0,18432]],[[0,0,0],[0,0,0],[0,0]],[[82944,-165888,82944],[-165888,172032,49152],[82944,49152]],[[0,0,0],[0,0,0],[0,0]],[[-55296,-387072,442368],[-387072,1226752,45056],[442368,45056]],[[0,0,0],[0,0,0],[0,0]],[[-3068928,2820096,995328],[2820096,3043328,16384],[995328,16384]],[[0,0,0],[0,0,0],[0,0]],[[-8448000,17670144,1228800],[17670144,4005888,2048],[1228800,2048]],[[0,0,0],[0,0],[0]],[[17781760,46753792,907264],[46753792,3117056],[907264]],[[0,0,0],[0,0],[0]],[[168718336,74782720,409600],[74782720,1472512],[409600]],[[0,0,0],[0,0],[0]],[[527128576,79966208,110592],[79966208,413696],[110592]],[[0,0,0],[0,0],[0]],[[1013569536,59506688,16384],[59506688,63488],[16384]],[[0,0,0],[0,0],[0]],[[1364156416,31238144,1024],[31238144,4096],[1024]],[[0,0],[0]],[[1352736768,11520000],[11520000]],[[0,0],[0]],[[1012195328,2918400],[2918400]],[[0,0],[0]],[[577177600,483328],[483328]],[[0,0],[0]],[[250917888,47104],[47104]],[[0,0],[0]],[[82497536,2048],[2048]],[[0]],[[20150272]],[[0]],[[3540992]],[[0]],[[422912]],[[0]],[[30720]],[[0]],[[1024]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
