/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode034
import Proofs.RadenkovicGutmanD39Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e057 : NestedArithmetic.Expr 3 := .times e034 e056
noncomputable def p057 : NestedHorner.Poly 3 := [[[0],[0]],[[0,-117],[-117]],[[0,0],[0]],[[-1755,-507],[-507]],[[0,0],[0]],[[-11700,-624],[-624]],[[0,0],[0]],[[-30381,-273],[-273]],[[0,0],[0]],[[-41184,-39],[-39]],[[0]],[[-32292]],[[0]],[[-15132]],[[0]],[[-4173]],[[0]],[[-624]],[[0]],[[-39]]]
theorem step057 : p057=NestedArithmetic.mul p034 p056 := by decide +kernel
#print axioms step057
theorem h057 : NestedArithmetic.compile e057=p057 := StagedExprCompile.compile_times e057 e034 e056 p034 p056 p057 rfl h034 h056 step057
#print axioms h057
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
