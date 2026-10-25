/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode289
import Proofs.RadenkovicGutmanD30Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[3600,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[108000,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1486800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[12448800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[70840800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[290037600,3600,0],[3600,0],[0]],[[0,0,0],[0,0],[0]],[[882298800,79200,0],[79200,0],[0]],[[0,0,0],[0,0],[0]],[[2030839200,774000,0],[774000,0],[0]],[[0,0,0],[0,0],[0]],[[3568759200,4428000,0],[4428000,0],[0]],[[0,0,0],[0,0],[0]],[[4796215200,16455600,0],[16455600,0],[0]],[[0,0,0],[0,0],[0]],[[4905687600,41688000,900],[41688000,1800],[900]],[[0,0,0],[0,0],[0]],[[3772591200,73533600,12600],[73533600,25200],[12600]],[[0,0,0],[0,0],[0]],[[2134706400,90648000,72900],[90648000,145800],[72900]],[[0,0,0],[0,0],[0]],[[857498400,77223600,225000],[77223600,450000],[225000]],[[0,0,0],[0,0],[0]],[[230072400,44172000,399600],[44172000,799200],[399600]],[[0,0,0],[0,0],[0]],[[36741600,16038000,412200],[16038000,824400],[412200]],[[0,0,0],[0,0],[0]],[[2624400,3304800,238500],[3304800,477000],[238500]],[[0,0,0],[0,0],[0]],[[0,291600,70200],[291600,140400],[70200]],[[0,0,0],[0,0],[0]],[[0,0,8100],[0,16200],[8100]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
