/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode164
import Proofs.RadenkovicGutmanD27Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-50],[0]],[[0,0],[0]],[[-742,0],[0,0]],[[0,0],[0,0]],[[-4588,0],[0,0]],[[0,0],[0,0]],[[-15302,0],[0,0]],[[0,0],[0,0]],[[-29800,0],[0,0]],[[0,0],[0,0]],[[-34248,-50],[-50,0]],[[0,0],[0,0]],[[-22036,-400],[-400,0]],[[0,0],[0,0]],[[-6230,-1100],[-1100,0]],[[0,0],[0,0]],[[474,-1200],[-1200,0]],[[0,0],[0,0]],[[522,-450],[-450,0]],[[0],[0,0]],[[0],[0,-50]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
