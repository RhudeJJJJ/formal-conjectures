/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode092
import Proofs.RadenkovicGutmanD15Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1080,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9720,-9720,0],[-9720,-9090,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-253530,-107730,0],[-107730,-29460,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2463210,-507060,0],[-507060,-47010,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12987360,-1338750,0],[-1338750,-39540,0],[0,0]],[[0,0,0],[0,0],[0]],[[-43138290,-2206020,0],[-2206020,-16680],[0]],[[0,0,0],[0,0],[0]],[[-97501590,-2378070,0],[-2378070,-2220],[0]],[[0,0,0],[0,0],[0]],[[-156733740,-1695720,0],[-1695720,750],[0]],[[0,0,0],[0,0],[0]],[[-183769440,-776820,0],[-776820,300],[0]],[[0,0,0],[0,0],[0]],[[-158982510,-201120,0],[-201120,30],[0]],[[0,0],[0]],[[-101304780,-10470],[-10470]],[[0,0],[0]],[[-46575660,11100],[11100]],[[0,0],[0]],[[-14514600,3810],[3810]],[[0,0],[0]],[[-2433870,540],[540]],[[0,0],[0]],[[156930,30],[30]],[[0]],[[215460]],[[0]],[[61560]],[[0]],[[9510]],[[0]],[[810]],[[0]],[[30]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
