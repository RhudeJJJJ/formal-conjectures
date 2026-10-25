/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode035
import Proofs.RadenkovicGutmanD18Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-2916],[0,-5832,1728],[-2916,1728]],[[0,0,0],[0,0,0],[0,0]],[[0,-80676,-9720],[-80676,11664,7488],[-9720,7488]],[[0,0,0],[0,0,0],[0,0]],[[-507384,-453924,23004],[-453924,263736,9216],[23004,9216]],[[0,0,0],[0,0,0],[0,0]],[[-3854952,43092,152280],[43092,905904,4032],[152280,4032]],[[0,0,0],[0,0,0],[0,0]],[[-3882168,6597864,292176],[6597864,1456416,576],[292176,576]],[[0,0,0],[0,0],[0]],[[62265024,24051924,285336],[24051924,1303344],[285336]],[[0,0,0],[0,0],[0]],[[353849904,45360540,157500],[45360540,682488],[157500]],[[0,0,0],[0,0],[0]],[[1000370160,53847216,49608],[53847216,207504],[49608]],[[0,0,0],[0,0],[0]],[[1834763112,43023636,8316],[43023636,33912],[8316]],[[0,0,0],[0,0],[0]],[[2380816872,23742396,576],[23742396,2304],[576]],[[0,0],[0]],[[2276834112,9074520],[9074520]],[[0,0],[0]],[[1638929592,2359260],[2359260]],[[0,0],[0]],[[896559768,398196],[398196]],[[0,0],[0]],[[373075920,39348],[39348]],[[0,0],[0]],[[117226512,1728],[1728]],[[0]],[[27338688]],[[0]],[[4584888]],[[0]],[[522504]],[[0]],[[36216]],[[0]],[[1152]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
