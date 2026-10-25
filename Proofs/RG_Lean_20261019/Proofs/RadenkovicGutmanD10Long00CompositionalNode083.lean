/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode070
import Proofs.RadenkovicGutmanD10Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,240],[0,240,296]],[[0,0,0],[0,0,0],[0,0,0]],[[0,2160,5760],[2160,14688,6608],[5760,6608,4]],[[0,0,0],[0,0,0],[0,0]],[[4536,196992,72456],[196992,217152,16600],[72456,16600]],[[0,0,0],[0,0,0],[0,0]],[[1278396,2446272,291076],[2446272,915888,15056],[291076,15056]],[[0,0,0],[0,0,0],[0,0]],[[18773640,12774680,574960],[12774680,1866336,5552],[574960,5552]],[[0,0,0],[0,0,0],[0,0]],[[121994124,37392352,648128],[37392352,2165824,736],[648128,736]],[[0,0,0],[0,0,0],[0,0]],[[467836760,69512096,443456],[69512096,1527616,8],[443456,8]],[[0,0,0],[0,0],[0]],[[1195679964,87587648,187384],[87587648,666368],[187384]],[[0,0,0],[0,0],[0]],[[2174473872,77527656,47888],[77527656,175968],[47888]],[[0,0,0],[0,0],[0]],[[2926510136,49085136,6848],[49085136,26016],[6848]],[[0,0,0],[0,0],[0]],[[2986798384,22338128,440],[22338128,1728],[440]],[[0,0,0],[0,0],[0]],[[2346233328,7251360,4],[7251360,16],[4]],[[0,0],[0]],[[1429735120,1640760],[1640760]],[[0,0],[0]],[[677210592,246880],[246880]],[[0,0],[0]],[[248409144,22480],[22480]],[[0,0],[0]],[[69852060,992],[992]],[[0,0],[0]],[[14780464,8],[8]],[[0]],[[2281080]],[[0]],[[243528]],[[0]],[[16316]],[[0]],[[552]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
