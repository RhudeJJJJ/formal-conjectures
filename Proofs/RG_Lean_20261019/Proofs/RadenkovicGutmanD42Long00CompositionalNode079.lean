/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode033
import Proofs.RadenkovicGutmanD42Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5292],[0,5292]],[[0,0,0],[0,0,0],[0,0]],[[0,-47628,47628],[-47628,174636,22932],[47628,22932]],[[0,0,0],[0,0,0],[0,0]],[[-714420,523908,333396],[523908,1195992,28224],[333396,28224]],[[0,0,0],[0,0,0],[0,0]],[[-4524660,7366464,920808],[7366464,3215772,12348],[920808,12348]],[[0,0,0],[0,0,0],[0,0]],[[2476656,33337836,1335348],[33337836,4533480,1764],[1335348,1764]],[[0,0,0],[0,0],[0]],[[116535132,82544616,1121904],[82544616,3704400],[1121904]],[[0,0,0],[0,0],[0]],[[553947156,129673404,562716],[129673404,1809864],[562716]],[[0,0,0],[0,0],[0]],[[1466183880,137969496,165816],[137969496,520380],[165816]],[[0,0,0],[0,0],[0]],[[2602499760,102539556,26460],[102539556,81144],[26460]],[[0,0,0],[0,0],[0]],[[3323861100,53814348,1764],[53814348,5292],[1764]],[[0,0],[0]],[[3161617200,19845000],[19845000]],[[0,0],[0]],[[2279518416,5027400],[5027400]],[[0,0],[0]],[[1254966048,832608],[832608]],[[0,0],[0]],[[527233140,81144],[81144]],[[0,0],[0]],[[167602932,3528],[3528]],[[0]],[[39594744]],[[0]],[[6731424]],[[0]],[[777924]],[[0]],[[54684]],[[0]],[[1764]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
