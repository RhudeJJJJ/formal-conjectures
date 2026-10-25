/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode119
import Proofs.RadenkovicGutmanD29Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-54],[0]],[[0,0],[0]],[[-802,0],[0,0]],[[0,0],[0,0]],[[-4964,0],[0,0]],[[0,0],[0,0]],[[-16578,0],[0,0]],[[0,0],[0,0]],[[-32344,0],[0,0]],[[0,0],[0,0]],[[-37272,-54],[-54,0]],[[0,0],[0,0]],[[-24092,-432],[-432,0]],[[0,0],[0,0]],[[-6898,-1188],[-1188,0]],[[0,0],[0,0]],[[462,-1296],[-1296,0]],[[0,0],[0,0]],[[558,-486],[-486,0]],[[0],[0,0]],[[0],[0,-54]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
