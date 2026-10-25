/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode036
import Proofs.RadenkovicGutmanD29Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-54]],[[0,0],[0]],[[558,-486],[-486]],[[0,0],[0]],[[462,-1296],[-1296]],[[0,0],[0]],[[-6898,-1188],[-1188]],[[0,0],[0]],[[-24092,-432],[-432]],[[0,0],[0]],[[-37272,-54],[-54]],[[0]],[[-32344]],[[0]],[[-16578]],[[0]],[[-4964]],[[0]],[[-802]],[[0]],[[-54]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
