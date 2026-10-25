/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode051
import Proofs.RadenkovicGutmanD9Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e051 e061
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,243],[0,243,-126]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-2187,3645],[-2187,10935,-1917],[3645,-1917,-28]],[[0,0,0],[0,0,0],[0,0]],[[-22599,65853,11421],[65853,13428,-8298],[11421,-8298]],[[0,0,0],[0,0,0],[0,0]],[[245349,433836,-15714],[433836,-175953,-10065],[-15714,-10065]],[[0,0,0],[0,0,0],[0,0]],[[3110940,416853,-121203],[416853,-689912,-4805],[-121203,-4805]],[[0,0,0],[0,0,0],[0,0]],[[9068895,-3508020,-232110],[-3508020,-1142152,-934],[-232110,-934]],[[0,0,0],[0,0,0],[0,0]],[[-11066511,-14814195,-227721],[-14814195,-1044990,-56],[-227721,-56]],[[0,0,0],[0,0],[0]],[[-147281764,-29126618,-129118],[-29126618,-567777],[-129118]],[[0,0,0],[0,0],[0]],[[-488962972,-35417723,-43321],[-35417723,-184948],[-43321]],[[0,0,0],[0,0],[0]],[[-965500057,-28945621,-8307],[-28945621,-34669],[-8307]],[[0,0,0],[0,0],[0]],[[-1312375570,-16418534,-808],[-16418534,-3306],[-808]],[[0,0,0],[0,0],[0]],[[-1300383124,-6514102,-28],[-6514102,-112],[-28]],[[0,0],[0]],[[-965747852,-1788198],[-1788198]],[[0,0],[0]],[[-544743271,-328772],[-328772]],[[0,0],[0]],[[-234242339,-37856],[-37856]],[[0,0],[0]],[[-76448632,-2372],[-2372]],[[0,0],[0]],[[-18689808,-56],[-56]],[[0]],[[-3339795]],[[0]],[[-418237]],[[0]],[[-34085]],[[0]],[[-1564]],[[0]],[[-28]]]
theorem step072 : p072=NestedArithmetic.mul p051 p061 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e051 e061 p051 p061 p072 rfl h051 h061 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
