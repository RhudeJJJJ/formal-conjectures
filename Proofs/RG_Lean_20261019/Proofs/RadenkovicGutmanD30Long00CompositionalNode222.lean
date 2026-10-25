/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode221
import Proofs.RadenkovicGutmanD30Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[1800,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[55800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[793800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[6868800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[40402800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[171025200,2700,0],[2700,0],[0]],[[0,0,0],[0,0],[0]],[[538036200,60300,0],[60300,0],[0]],[[0,0,0],[0,0],[0]],[[1281040200,598500,0],[598500,0],[0]],[[0,0,0],[0,0],[0]],[[2328955200,3479400,0],[3479400,0],[0]],[[0,0,0],[0,0],[0]],[[3238162200,13148100,0],[13148100,0],[0]],[[0,0,0],[0,0],[0]],[[3425765400,33893100,900],[33893100,1800],[900]],[[0,0,0],[0,0],[0]],[[2723504400,60872400,12600],[60872400,25200],[12600]],[[0,0,0],[0,0],[0]],[[1591736400,76443300,72900],[76443300,145800],[72900]],[[0,0,0],[0,0],[0]],[[659534400,66350700,225000],[66350700,450000],[225000]],[[0,0,0],[0,0],[0]],[[182201400,38655000,399600],[38655000,799200],[399600]],[[0,0,0],[0,0],[0]],[[29889000,14280300,412200],[14280300,824400],[412200]],[[0,0,0],[0,0],[0]],[[2187000,2988900,238500],[2988900,477000],[238500]],[[0,0,0],[0,0],[0]],[[0,267300,70200],[267300,140400],[70200]],[[0,0,0],[0,0],[0]],[[0,0,8100],[0,16200],[8100]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
