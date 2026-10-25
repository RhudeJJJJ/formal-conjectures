/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode194
import Proofs.RadenkovicGutmanD42Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[84],[0]],[[0,0],[0]],[[1344,0],[0]],[[0,0],[0]],[[8988,0],[0]],[[0,0],[0]],[[32592,0],[0]],[[0,0],[0]],[[69552,0],[0]],[[0,0],[0]],[[88704,84],[84]],[[0,0],[0]],[[65436,588],[588]],[[0,0],[0]],[[25200,1344],[1344]],[[0,0],[0]],[[3780,1092],[1092]],[[0,0],[0]],[[0,252],[252]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
