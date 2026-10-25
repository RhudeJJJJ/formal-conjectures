/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode093
import Proofs.RadenkovicGutmanD22Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,484]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-4356],[0,-8712,14256],[-4356,14256,44]],[[0,0,0],[0,0,0],[0,0]],[[-39204,-146124,51348],[-146124,272184,48048],[51348,48048]],[[0,0,0],[0,0,0],[0,0]],[[-1823580,336204,433664],[336204,1915672,52976],[433664,52976]],[[0,0,0],[0,0,0],[0,0]],[[-10146708,9992268,1232440],[9992268,5116584,22616],[1232440,22616]],[[0,0,0],[0,0,0],[0,0]],[[7339596,49589232,1807608],[49589232,7216880,3520],[1807608,3520]],[[0,0,0],[0,0,0],[0,0]],[[262135412,127555604,1535952],[127555604,5956016,88],[1535952,88]],[[0,0,0],[0,0],[0]],[[1219961996,205011180,782892],[205011180,2967976],[782892]],[[0,0,0],[0,0],[0]],[[3191335928,221719784,236808],[221719784,882376],[236808]],[[0,0,0],[0,0],[0]],[[5608980960,166982860,39732],[166982860,146344],[39732]],[[0,0,0],[0,0],[0]],[[7094037984,88730180,3036],[88730180,11176],[3036]],[[0,0,0],[0,0],[0]],[[6681221184,33176528,44],[33176528,176],[44]],[[0,0],[0]],[[4770536936,8561300],[8561300]],[[0,0],[0]],[[2603039032,1460052],[1460052]],[[0,0],[0]],[[1085616532,150612],[150612]],[[0,0],[0]],[[343524236,7656],[7656]],[[0,0],[0]],[[81136968,88],[88]],[[0]],[[13893264]],[[0]],[[1639836]],[[0]],[[121572]],[[0]],[[4620]],[[0]],[[44]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
