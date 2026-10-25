/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,49]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-882,882],[0,882]],[[0,0,0],[0,0,0],[0,0]],[[3969,-7938,3969],[-7938,8232,2352],[3969,2352]],[[0,0,0],[0,0,0],[0,0]],[[-2646,-18522,21168],[-18522,58702,2156],[21168,2156]],[[0,0,0],[0,0,0],[0,0]],[[-146853,134946,47628],[134946,145628,784],[47628,784]],[[0,0,0],[0,0,0],[0,0]],[[-404250,845544,58800],[845544,191688,98],[58800,98]],[[0,0,0],[0,0],[0]],[[850885,2237242,43414],[2237242,149156],[43414]],[[0,0,0],[0,0],[0]],[[8073436,3578470,19600],[3578470,70462],[19600]],[[0,0,0],[0,0],[0]],[[25223926,3826508,5292],[3826508,19796],[5292]],[[0,0,0],[0,0],[0]],[[48500886,2847488,784],[2847488,3038],[784]],[[0,0,0],[0,0],[0]],[[65277016,1494794,49],[1494794,196],[49]],[[0,0],[0]],[[64730568,551250],[551250]],[[0,0],[0]],[[48435128,139650],[139650]],[[0,0],[0]],[[27618850,23128],[23128]],[[0,0],[0]],[[12006813,2254],[2254]],[[0,0],[0]],[[3947636,98],[98]],[[0]],[[964222]],[[0]],[[169442]],[[0]],[[20237]],[[0]],[[1470]],[[0]],[[49]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
