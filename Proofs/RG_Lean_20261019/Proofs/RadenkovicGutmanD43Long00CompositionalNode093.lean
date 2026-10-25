/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode033
import Proofs.RadenkovicGutmanD43Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1849]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,44376],[0,44376,86]],[[0,0,0],[0,0,0],[0,0]],[[-149769,-99846,249615],[-99846,965178,138374],[249615,138374]],[[0,0,0],[0,0,0],[0,0]],[[-4100652,3794148,1504656],[3794148,5730180,144652],[1504656,144652]],[[0,0,0],[0,0,0],[0,0]],[[-17543871,37134972,3764736],[37134972,14078974,59254],[3764736,59254]],[[0,0,0],[0,0,0],[0,0]],[[42542394,148172410,5101778],[148172410,18713428,8772],[5101778,8772]],[[0,0,0],[0,0,0],[0,0]],[[605543501,340386108,4093342],[340386108,14731456,172],[4093342,172]],[[0,0,0],[0,0],[0]],[[2505034316,507607948,1995458],[507607948,7057332],[1995458]],[[0,0,0],[0,0],[0]],[[6166961530,519774368,581704],[519774368,2027278],[581704]],[[0,0,0],[0,0],[0]],[[10424571872,375462154,94342],[375462154,325596],[94342]],[[0,0,0],[0,0],[0]],[[12839833970,193113430,6923],[193113430,23994],[6923]],[[0,0,0],[0,0],[0]],[[11875735700,70362018,86],[70362018,344],[86]],[[0,0],[0]],[[8377895712,17783080],[17783080]],[[0,0],[0]],[[4536870488,2981620],[2981620]],[[0,0],[0]],[[1884217129,303236],[303236]],[[0,0],[0]],[[595299396,15222],[15222]],[[0,0],[0]],[[140690754,172],[172]],[[0]],[[24154648]],[[0]],[[2865305]],[[0]],[[214312]],[[0]],[[8299]],[[0]],[[86]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
