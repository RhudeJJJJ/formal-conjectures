/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode033
import Proofs.RadenkovicGutmanD4Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e034 : NestedArithmetic.Expr 3 := .times e033 e028
noncomputable def p034 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-12],[-12]],[[0,0],[0]],[[-216,-52],[-52]],[[0,0],[0]],[[-1512,-64],[-64]],[[0,0],[0]],[[-4176,-28],[-28]],[[0,0],[0]],[[-6056,-4],[-4]],[[0]],[[-5088]],[[0]],[[-2552]],[[0]],[[-752]],[[0]],[[-120]],[[0]],[[-8]]]
theorem step034 : p034=NestedArithmetic.mul p033 p028 := by decide +kernel
#print axioms step034
theorem h034 : NestedArithmetic.compile e034=p034 := StagedExprCompile.compile_times e034 e033 e028 p033 p028 p034 rfl h033 h028 step034
#print axioms h034
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
