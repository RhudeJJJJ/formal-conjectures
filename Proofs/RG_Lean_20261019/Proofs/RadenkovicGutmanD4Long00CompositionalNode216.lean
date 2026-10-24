/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode033
import Proofs.RadenkovicGutmanD4Long00CompositionalNode182
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e216 : NestedArithmetic.Expr 3 := .times e033 e182
noncomputable def p216 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-64,0],[0]],[[0,0],[0]],[[-428,0],[0]],[[0,0],[0]],[[-1552,0],[0]],[[0,0],[0]],[[-3312,0],[0]],[[0,0],[0]],[[-4224,-4],[-4]],[[0,0],[0]],[[-3116,-28],[-28]],[[0,0],[0]],[[-1200,-64],[-64]],[[0,0],[0]],[[-180,-52],[-52]],[[0,0],[0]],[[0,-12],[-12]]]
theorem step216 : p216=NestedArithmetic.mul p033 p182 := by decide +kernel
#print axioms step216
theorem h216 : NestedArithmetic.compile e216=p216 := StagedExprCompile.compile_times e216 e033 e182 p033 p182 p216 rfl h033 h182 step216
#print axioms h216
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
