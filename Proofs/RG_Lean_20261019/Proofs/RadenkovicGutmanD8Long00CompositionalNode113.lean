/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,64]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1152,1152],[0,1152]],[[0,0,0],[0,0,0],[0,0]],[[5184,-10368,5184],[-10368,10752,3072],[5184,3072]],[[0,0,0],[0,0,0],[0,0]],[[-3456,-24192,27648],[-24192,76672,2816],[27648,2816]],[[0,0,0],[0,0,0],[0,0]],[[-191808,176256,62208],[176256,190208,1024],[62208,1024]],[[0,0,0],[0,0,0],[0,0]],[[-528000,1104384,76800],[1104384,250368,128],[76800,128]],[[0,0,0],[0,0],[0]],[[1111360,2922112,56704],[2922112,194816],[56704]],[[0,0,0],[0,0],[0]],[[10544896,4673920,25600],[4673920,92032],[25600]],[[0,0,0],[0,0],[0]],[[32945536,4997888,6912],[4997888,25856],[6912]],[[0,0,0],[0,0],[0]],[[63348096,3719168,1024],[3719168,3968],[1024]],[[0,0,0],[0,0],[0]],[[85259776,1952384,64],[1952384,256],[64]],[[0,0],[0]],[[84546048,720000],[720000]],[[0,0],[0]],[[63262208,182400],[182400]],[[0,0],[0]],[[36073600,30208],[30208]],[[0,0],[0]],[[15682368,2944],[2944]],[[0,0],[0]],[[5156096,128],[128]],[[0]],[[1259392]],[[0]],[[221312]],[[0]],[[26432]],[[0]],[[1920]],[[0]],[[64]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
