/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode034
import Proofs.RadenkovicGutmanD28Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-56],[0]],[[0,0],[0]],[[-840,0],[0]],[[0,0],[0]],[[-5264,0],[0]],[[0,0],[0]],[[-17864,0],[0]],[[0,0],[0]],[[-35616,0],[0]],[[0,0],[0]],[[-42392,-28],[-28]],[[0,0],[0]],[[-29232,-196],[-196]],[[0,0],[0]],[[-10584,-448],[-448]],[[0,0],[0]],[[-1512,-364],[-364]],[[0,0],[0]],[[0,-84],[-84]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
