/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode058
import Proofs.RadenkovicGutmanD32Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-60]],[[0,0],[0]],[[-540,-540],[-540]],[[0,0],[0]],[[-9540,-1440],[-1440]],[[0,0],[0]],[[-41820,-1320],[-1320]],[[0,0],[0]],[[-85800,-480],[-480]],[[0,0],[0]],[[-98640,-60],[-60]],[[0]],[[-68160]],[[0]],[[-28860]],[[0]],[[-7320]],[[0]],[[-1020]],[[0]],[[-60]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
