/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode030
import Proofs.RadenkovicGutmanD33Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e060 : NestedArithmetic.Expr 3 := .times e030 e056
noncomputable def p060 : NestedHorner.Poly 3 := [[[0],[0]],[[0,99],[99]],[[0,0],[0]],[[1485,429],[429]],[[0,0],[0]],[[9900,528],[528]],[[0,0],[0]],[[25707,231],[231]],[[0,0],[0]],[[34848,33],[33]],[[0]],[[27324]],[[0]],[[12804]],[[0]],[[3531]],[[0]],[[528]],[[0]],[[33]]]
theorem step060 : p060=NestedArithmetic.mul p030 p056 := by decide +kernel
#print axioms step060
theorem h060 : NestedArithmetic.compile e060=p060 := StagedExprCompile.compile_times e060 e030 e056 p030 p056 p060 rfl h030 h056 step060
#print axioms h060
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
