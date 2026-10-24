/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode033
import Proofs.RadenkovicGutmanD4Long00CompositionalNode169
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e215 : NestedArithmetic.Expr 3 := .times e033 e169
noncomputable def p215 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-120,0],[0]],[[0,0],[0]],[[-752,0],[0]],[[0,0],[0]],[[-2552,0],[0]],[[0,0],[0]],[[-5088,0],[0]],[[0,0],[0]],[[-6056,-4],[-4]],[[0,0],[0]],[[-4176,-28],[-28]],[[0,0],[0]],[[-1512,-64],[-64]],[[0,0],[0]],[[-216,-52],[-52]],[[0,0],[0]],[[0,-12],[-12]]]
theorem step215 : p215=NestedArithmetic.mul p033 p169 := by decide +kernel
#print axioms step215
theorem h215 : NestedArithmetic.compile e215=p215 := StagedExprCompile.compile_times e215 e033 e169 p033 p169 p215 rfl h033 h169 step215
#print axioms h215
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
