/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode043
import Proofs.RadenkovicGutmanD4Long00CompositionalNode031
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e044 : NestedArithmetic.Expr 3 := .times e043 e031
noncomputable def p044 : NestedHorner.Poly 3 := [[[0],[0,4]],[[0,0],[0,0]],[[-36,36],[36,2]],[[0,0],[0]],[[-6,114],[114]],[[0,0],[0]],[[674,136],[136]],[[0,0],[0]],[[2390,76],[76]],[[0,0],[0]],[[4052,20],[20]],[[0,0],[0]],[[4056,2],[2]],[[0]],[[2548]],[[0]],[[1014]],[[0]],[[248]],[[0]],[[34]],[[0]],[[2]]]
theorem step044 : p044=NestedArithmetic.mul p043 p031 := by decide +kernel
#print axioms step044
theorem h044 : NestedArithmetic.compile e044=p044 := StagedExprCompile.compile_times e044 e043 e031 p043 p031 p044 rfl h043 h031 step044
#print axioms h044
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
