/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode058
import Proofs.RadenkovicGutmanD30Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-56]],[[0,0],[0]],[[-504,-504],[-504]],[[0,0],[0]],[[-8904,-1344],[-1344]],[[0,0],[0]],[[-39032,-1232],[-1232]],[[0,0],[0]],[[-80080,-448],[-448]],[[0,0],[0]],[[-92064,-56],[-56]],[[0]],[[-63616]],[[0]],[[-26936]],[[0]],[[-6832]],[[0]],[[-952]],[[0]],[[-56]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
