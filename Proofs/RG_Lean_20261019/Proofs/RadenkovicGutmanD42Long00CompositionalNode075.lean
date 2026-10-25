/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode033
import Proofs.RadenkovicGutmanD42Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1764]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,31752],[0,31752]],[[0,0,0],[0,0,0],[0,0]],[[-142884,0,142884],[0,571536,84672],[142884,84672]],[[0,0,0],[0,0,0],[0,0]],[[-2476656,2571912,762048],[2571912,3048192,77616],[762048,77616]],[[0,0,0],[0,0,0],[0,0]],[[-7572852,20575296,1714608],[20575296,6858432,28224],[1714608,28224]],[[0,0,0],[0,0,0],[0,0]],[[35985600,73728144,2116800],[73728144,8467200,3528],[2116800,3528]],[[0,0,0],[0,0],[0]],[[342962172,156219840,1562904],[156219840,6251616],[1562904]],[[0,0,0],[0,0],[0]],[[1266029856,217659960,705600],[217659960,2822400],[705600]],[[0,0,0],[0,0],[0]],[[2892208536,209817216,190512],[209817216,762048],[190512]],[[0,0,0],[0,0],[0]],[[4605825168,143363808,28224],[143363808,112896],[28224]],[[0,0,0],[0,0],[0]],[[5387629968,69939072,1764],[69939072,7056],[1764]],[[0,0],[0]],[[4755976848,24184440],[24184440]],[[0,0],[0]],[[3212512128,5785920],[5785920]],[[0,0],[0]],[[1668955680,910224],[910224]],[[0,0],[0]],[[665506044,84672],[84672]],[[0,0],[0]],[[201773376,3528],[3528]],[[0]],[[45648792]],[[0]],[[7458192]],[[0]],[[830844]],[[0]],[[56448]],[[0]],[[1764]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
