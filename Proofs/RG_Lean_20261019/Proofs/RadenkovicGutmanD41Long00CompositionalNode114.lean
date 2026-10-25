/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,15129],[0,30258],[15129]],[[0,0,0],[0,0],[0]],[[0,544644,131118],[544644,262236],[131118]],[[0,0,0],[0,0],[0]],[[4901796,6172632,445465],[6172632,890930],[445465]],[[0,0,0],[0,0],[0]],[[68625144,29955420,769898],[29955420,1539796],[769898]],[[0,0,0],[0,0],[0]],[[429724116,82503480,746364],[82503480,1492728],[746364]],[[0,0,0],[0,0],[0]],[[1601616456,144236524,420250],[144236524,840500],[420250]],[[0,0,0],[0,0],[0]],[[3987157176,169310320,136161],[169310320,272322],[136161]],[[0,0,0],[0,0],[0]],[[7046362008,137344424,23534],[137344424,47068],[23534]],[[0,0,0],[0,0],[0]],[[9162734284,77863920,1681],[77863920,3362],[1681]],[[0,0],[0]],[[8958264168,30735404],[30735404]],[[0,0],[0]],[[6665649128,8270520],[8270520]],[[0,0],[0]],[[3793156328,1445660],[1445660]],[[0,0],[0]],[[1647938092,147928],[147928]],[[0,0],[0]],[[541725784,6724],[6724]],[[0]],[[132314872]],[[0]],[[23251592]],[[0]],[[2777012]],[[0]],[[201720]],[[0]],[[6724]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
