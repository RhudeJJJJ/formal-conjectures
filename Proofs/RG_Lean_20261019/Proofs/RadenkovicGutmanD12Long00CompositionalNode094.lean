/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode035
import Proofs.RadenkovicGutmanD12Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-1296],[0,-2592,720],[-1296,720]],[[0,0,0],[0,0,0],[0,0]],[[0,-36288,-4752],[-36288,3456,3120],[-4752,3120]],[[0,0,0],[0,0,0],[0,0]],[[-233280,-219024,7200],[-219024,105120,3840],[7200,3840]],[[0,0,0],[0,0,0],[0,0]],[[-1905120,-124848,59328],[-124848,369216,1680],[59328,1680]],[[0,0,0],[0,0,0],[0,0]],[[-3439584,2362560,117744],[2362560,598848,240],[117744,240]],[[0,0,0],[0,0],[0]],[[19348416,9358128,116640],[9358128,538560],[116640]],[[0,0,0],[0,0],[0]],[[131520096,18135792,64896],[18135792,282912],[64896]],[[0,0,0],[0,0],[0]],[[389585856,21827616,20544],[21827616,86208],[20544]],[[0,0,0],[0,0],[0]],[[730226976,17587584,3456],[17587584,14112],[3456]],[[0,0,0],[0,0],[0]],[[959625408,9761184,240],[9761184,960],[240]],[[0,0],[0]],[[925391328,3746256],[3746256]],[[0,0],[0]],[[670076928,977040],[977040]],[[0,0],[0]],[[368186208,165312],[165312]],[[0,0],[0]],[[153738048,16368],[16368]],[[0,0],[0]],[[48440352,720],[720]],[[0]],[[11322432]],[[0]],[[1902432]],[[0]],[[217152]],[[0]],[[15072]],[[0]],[[480]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
