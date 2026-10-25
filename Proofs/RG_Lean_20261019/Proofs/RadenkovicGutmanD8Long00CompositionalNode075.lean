/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode033
import Proofs.RadenkovicGutmanD8Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,64]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,1152],[0,1152]],[[0,0,0],[0,0,0],[0,0]],[[-5184,0,5184],[0,20736,3072],[5184,3072]],[[0,0,0],[0,0,0],[0,0]],[[-89856,93312,27648],[93312,110592,2816],[27648,2816]],[[0,0,0],[0,0,0],[0,0]],[[-274752,746496,62208],[746496,248832,1024],[62208,1024]],[[0,0,0],[0,0,0],[0,0]],[[1305600,2674944,76800],[2674944,307200,128],[76800,128]],[[0,0,0],[0,0],[0]],[[12443072,5667840,56704],[5667840,226816],[56704]],[[0,0,0],[0,0],[0]],[[45933056,7896960,25600],[7896960,102400],[25600]],[[0,0,0],[0,0],[0]],[[104932736,7612416,6912],[7612416,27648],[6912]],[[0,0,0],[0,0],[0]],[[167104768,5201408,1024],[5201408,4096],[1024]],[[0,0,0],[0,0],[0]],[[195469568,2537472,64],[2537472,256],[64]],[[0,0],[0]],[[172552448,877440],[877440]],[[0,0],[0]],[[116553728,209920],[209920]],[[0,0],[0]],[[60551680,33024],[33024]],[[0,0],[0]],[[24145344,3072],[3072]],[[0,0],[0]],[[7320576,128],[128]],[[0]],[[1656192]],[[0]],[[270592]],[[0]],[[30144]],[[0]],[[2048]],[[0]],[[64]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
