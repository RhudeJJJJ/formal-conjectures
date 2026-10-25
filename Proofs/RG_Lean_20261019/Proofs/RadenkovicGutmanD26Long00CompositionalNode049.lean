/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode045
import Proofs.RadenkovicGutmanD26Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,26]],[[0,0],[0,0]],[[-234,390],[390,2]],[[0,0],[0]],[[2868,1318],[1318]],[[0,0],[0]],[[24004,1452],[1452]],[[0,0],[0]],[[67986,616],[616]],[[0,0],[0]],[[99412,94],[94]],[[0,0],[0]],[[84192,2],[2]],[[0]],[[42742]],[[0]],[[12858]],[[0]],[[2138]],[[0]],[[160]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
