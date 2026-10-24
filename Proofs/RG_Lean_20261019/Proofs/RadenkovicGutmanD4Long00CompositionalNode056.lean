/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode033
import Proofs.RadenkovicGutmanD4Long00CompositionalNode055
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e056 : NestedArithmetic.Expr 3 := .times e033 e055
noncomputable def p056 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-12],[-12]],[[0,0],[0]],[[-180,-52],[-52]],[[0,0],[0]],[[-1200,-64],[-64]],[[0,0],[0]],[[-3116,-28],[-28]],[[0,0],[0]],[[-4224,-4],[-4]],[[0]],[[-3312]],[[0]],[[-1552]],[[0]],[[-428]],[[0]],[[-64]],[[0]],[[-4]]]
theorem step056 : p056=NestedArithmetic.mul p033 p055 := by decide +kernel
#print axioms step056
theorem h056 : NestedArithmetic.compile e056=p056 := StagedExprCompile.compile_times e056 e033 e055 p033 p055 p056 rfl h033 h055 step056
#print axioms h056
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
