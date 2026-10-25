/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode036
import Proofs.RadenkovicGutmanD37Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-70]],[[0,0],[0]],[[702,-630],[-630]],[[0,0],[0]],[[414,-1680],[-1680]],[[0,0],[0]],[[-9570,-1540],[-1540]],[[0,0],[0]],[[-32316,-560],[-560]],[[0,0],[0]],[[-49368,-70],[-70]],[[0]],[[-42520]],[[0]],[[-21682]],[[0]],[[-6468]],[[0]],[[-1042]],[[0]],[[-70]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
