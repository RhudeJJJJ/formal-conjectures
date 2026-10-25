/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode058
import Proofs.RadenkovicGutmanD42Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-80]],[[0,0],[0]],[[-720,-720],[-720]],[[0,0],[0]],[[-12720,-1920],[-1920]],[[0,0],[0]],[[-55760,-1760],[-1760]],[[0,0],[0]],[[-114400,-640],[-640]],[[0,0],[0]],[[-131520,-80],[-80]],[[0]],[[-90880]],[[0]],[[-38480]],[[0]],[[-9760]],[[0]],[[-1360]],[[0]],[[-80]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
