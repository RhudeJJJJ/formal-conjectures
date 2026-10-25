/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode095
import Proofs.RadenkovicGutmanD13Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-936,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8424,-8424,0],[-8424,-8112,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-221832,-95472,0],[-95472,-27560,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2190240,-463320,0],[-463320,-47632,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11803272,-1276080,0],[-1276080,-46176,0],[0,0]],[[0,0,0],[0,0],[0]],[[-40337336,-2230904,0],[-2230904,-26000],[0]],[[0,0,0],[0,0],[0]],[[-94585712,-2618720,0],[-2618720,-8424],[0]],[[0,0,0],[0,0],[0]],[[-159482336,-2124304,0],[-2124304,-1456],[0]],[[0,0,0],[0,0],[0]],[[-199137432,-1204320,0],[-1204320,-104],[0]],[[0,0,0],[0,0],[0]],[[-187569200,-475384,0],[-475384,0],[0]],[[0,0],[0]],[[-134689776,-127920],[-127920]],[[0,0],[0]],[[-74038016,-22360],[-22360]],[[0,0],[0]],[[-31088824,-2288],[-2288]],[[0,0],[0]],[[-9881560,-104],[-104]],[[0,0],[0]],[[-2334384,0],[0]],[[0]],[[-396864]],[[0]],[[-45864]],[[0]],[[-3224]],[[0]],[[-104]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
