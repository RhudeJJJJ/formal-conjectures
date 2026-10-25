/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,23814,0],[23814,3969,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[392931,345303,0],[345303,34398,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[6417873,2127384,0],[2127384,116865,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[46627812,7371315,0],[7371315,201978,0],[0,0]],[[0,0,0],[0,0],[0]],[[200322045,16066512,0],[16066512,195804],[0]],[[0,0,0],[0,0],[0]],[[571151889,23380497,0],[23380497,110250],[0]],[[0,0,0],[0,0],[0]],[[1150028334,23512356,0],[23512356,35721],[0]],[[0,0,0],[0,0],[0]],[[1698342156,16646868,0],[16646868,6174],[0]],[[0,0,0],[0,0],[0]],[[1884366099,8348130,0],[8348130,441],[0]],[[0,0],[0]],[[1594715094,2945439],[2945439]],[[0,0],[0]],[[1038012570,714420],[714420]],[[0,0],[0]],[[520983288,113337],[113337]],[[0,0],[0]],[[200966787,10584],[10584]],[[0,0],[0]],[[58986837,441],[441]],[[0]],[[12925710]],[[0]],[[2046240]],[[0]],[[220941]],[[0]],[[14553]],[[0]],[[441]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
