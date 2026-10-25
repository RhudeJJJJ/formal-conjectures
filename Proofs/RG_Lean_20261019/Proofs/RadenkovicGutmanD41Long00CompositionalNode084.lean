/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,90774,0],[90774,15129,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1497771,1316223,0],[1316223,131118,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[24463593,8109144,0],[8109144,445465,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[177735492,28097915,0],[28097915,769898,0],[0,0]],[[0,0,0],[0,0],[0]],[[763585845,61242192,0],[61242192,746364],[0]],[[0,0,0],[0,0],[0]],[[2177111849,89121577,0],[89121577,420250],[0]],[[0,0,0],[0,0],[0]],[[4383668094,89624196,0],[89624196,136161],[0]],[[0,0,0],[0,0],[0]],[[6473725996,63454388,0],[63454388,23534],[0]],[[0,0,0],[0,0],[0]],[[7182810459,31821330,0],[31821330,1681],[0]],[[0,0],[0]],[[6078721254,11227399],[11227399]],[[0,0],[0]],[[3956687370,2723220],[2723220]],[[0,0],[0]],[[1985879608,432017],[432017]],[[0,0],[0]],[[766043467,40344],[40344]],[[0,0],[0]],[[224845517,1681],[1681]],[[0]],[[49270110]],[[0]],[[7799840]],[[0]],[[842181]],[[0]],[[55473]],[[0]],[[1681]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
