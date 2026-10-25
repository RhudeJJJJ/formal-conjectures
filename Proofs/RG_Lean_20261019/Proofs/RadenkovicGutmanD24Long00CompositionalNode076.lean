/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode035
import Proofs.RadenkovicGutmanD24Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-5184],[0,-10368],[-5184]],[[0,0,0],[0,0],[0]],[[0,-171072,-44928],[-171072,-89856],[-44928]],[[0,0,0],[0,0],[0]],[[-1399680,-1912896,-152640],[-1912896,-305280],[-152640]],[[0,0,0],[0,0],[0]],[[-19128960,-9139392,-263808],[-9139392,-527616],[-263808]],[[0,0,0],[0,0],[0]],[[-116608896,-24739200,-255744],[-24739200,-511488],[-255744]],[[0,0,0],[0,0],[0]],[[-422102016,-42464448,-144000],[-42464448,-288000],[-144000]],[[0,0,0],[0,0],[0]],[[-1018711296,-48923712,-46656],[-48923712,-93312],[-46656]],[[0,0,0],[0,0],[0]],[[-1743042816,-38958336,-8064],[-38958336,-16128],[-8064]],[[0,0,0],[0,0],[0]],[[-2192489856,-21691584,-576],[-21691584,-1152],[-576]],[[0,0],[0]],[[-2072423808,-8414784],[-8414784]],[[0,0],[0]],[[-1490531328,-2226816],[-2226816]],[[0,0],[0]],[[-819865728,-383040],[-383040]],[[0,0],[0]],[[-344343168,-38592],[-38592]],[[0,0],[0]],[[-109456128,-1728],[-1728]],[[0]],[[-25857792]],[[0]],[[-4396032]],[[0]],[[-508032]],[[0]],[[-35712]],[[0]],[[-1152]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
