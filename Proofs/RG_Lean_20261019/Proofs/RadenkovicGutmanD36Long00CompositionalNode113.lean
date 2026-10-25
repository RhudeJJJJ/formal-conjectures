/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1296]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-23328,23328],[0,23328]],[[0,0,0],[0,0,0],[0,0]],[[104976,-209952,104976],[-209952,217728,62208],[104976,62208]],[[0,0,0],[0,0,0],[0,0]],[[-69984,-489888,559872],[-489888,1552608,57024],[559872,57024]],[[0,0,0],[0,0,0],[0,0]],[[-3884112,3569184,1259712],[3569184,3851712,20736],[1259712,20736]],[[0,0,0],[0,0,0],[0,0]],[[-10692000,22363776,1555200],[22363776,5069952,2592],[1555200,2592]],[[0,0,0],[0,0],[0]],[[22505040,59172768,1148256],[59172768,3945024],[1148256]],[[0,0,0],[0,0],[0]],[[213534144,94646880,518400],[94646880,1863648],[518400]],[[0,0,0],[0,0],[0]],[[667147104,101207232,139968],[101207232,523584],[139968]],[[0,0,0],[0,0],[0]],[[1282798944,75313152,20736],[75313152,80352],[20736]],[[0,0,0],[0,0],[0]],[[1726510464,39535776,1296],[39535776,5184],[1296]],[[0,0],[0]],[[1712057472,14580000],[14580000]],[[0,0],[0]],[[1281059712,3693600],[3693600]],[[0,0],[0]],[[730490400,611712],[611712]],[[0,0],[0]],[[317567952,59616],[59616]],[[0,0],[0]],[[104410944,2592],[2592]],[[0]],[[25502688]],[[0]],[[4481568]],[[0]],[[535248]],[[0]],[[38880]],[[0]],[[1296]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
