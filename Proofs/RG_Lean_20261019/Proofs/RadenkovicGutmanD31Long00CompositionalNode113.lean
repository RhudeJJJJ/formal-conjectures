/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,961]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-17298,17298],[0,17298]],[[0,0,0],[0,0,0],[0,0]],[[77841,-155682,77841],[-155682,161448,46128],[77841,46128]],[[0,0,0],[0,0,0],[0,0]],[[-51894,-363258,415152],[-363258,1151278,42284],[415152,42284]],[[0,0,0],[0,0,0],[0,0]],[[-2880117,2646594,934092],[2646594,2856092,15376],[934092,15376]],[[0,0,0],[0,0,0],[0,0]],[[-7928250,16583016,1153200],[16583016,3759432,1922],[1153200,1922]],[[0,0,0],[0,0],[0]],[[16687765,43877338,851446],[43877338,2925284],[851446]],[[0,0,0],[0,0],[0]],[[158338204,70181830,384400],[70181830,1381918],[384400]],[[0,0,0],[0,0],[0]],[[494697814,75046412,103788],[75046412,388244],[103788]],[[0,0,0],[0,0],[0]],[[951211254,55845632,15376],[55845632,59582],[15376]],[[0,0,0],[0,0],[0]],[[1280228824,29316266,961],[29316266,3844],[961]],[[0,0],[0]],[[1269511752,10811250],[10811250]],[[0,0],[0]],[[949921592,2738850],[2738850]],[[0,0],[0]],[[541667650,453592],[453592]],[[0,0],[0]],[[235480557,44206],[44206]],[[0,0],[0]],[[77422004,1922],[1922]],[[0]],[[18910558]],[[0]],[[3323138]],[[0]],[[396893]],[[0]],[[28830]],[[0]],[[961]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
