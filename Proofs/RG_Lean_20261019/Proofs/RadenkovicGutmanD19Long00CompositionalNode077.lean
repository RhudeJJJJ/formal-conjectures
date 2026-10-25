/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,3249],[0,6498],[3249]],[[0,0,0],[0,0],[0]],[[0,107217,28158],[107217,56316],[28158]],[[0,0,0],[0,0],[0]],[[877230,1198881,95665],[1198881,191330],[95665]],[[0,0,0],[0,0],[0]],[[11988810,5727987,165338],[5727987,330676],[165338]],[[0,0,0],[0,0],[0]],[[73083006,15504950,160284],[15504950,320568],[160284]],[[0,0,0],[0,0],[0]],[[264546576,26614003,90250],[26614003,180500],[90250]],[[0,0,0],[0,0],[0]],[[638463156,30662257,29241],[30662257,58482],[29241]],[[0,0,0],[0,0],[0]],[[1092427876,24416596,5054],[24416596,10108],[5054]],[[0,0,0],[0,0],[0]],[[1374112566,13594899,361],[13594899,722],[361]],[[0,0],[0]],[[1298862838,5273849],[5273849]],[[0,0],[0]],[[934169808,1395626],[1395626]],[[0,0],[0]],[[513839458,240065],[240065]],[[0,0],[0]],[[215812298,24187],[24187]],[[0,0],[0]],[[68600108,1083],[1083]],[[0]],[[16206012]],[[0]],[[2755152]],[[0]],[[318402]],[[0]],[[22382]],[[0]],[[722]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
