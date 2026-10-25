/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode081
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .scaled (-1) e081
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,51894,0],[51894,8649,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[856251,752463,0],[752463,74958,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[13985433,4635864,0],[4635864,254665,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[101608452,16063115,0],[16063115,440138,0],[0,0]],[[0,0,0],[0,0],[0]],[[436529445,35011152,0],[35011152,426684],[0]],[[0,0,0],[0,0],[0]],[[1244618969,50949337,0],[50949337,240250],[0]],[[0,0,0],[0,0],[0]],[[2506070814,51236676,0],[51236676,77841],[0]],[[0,0,0],[0,0],[0]],[[3700922476,36275828,0],[36275828,13454],[0]],[[0,0,0],[0,0],[0]],[[4106294379,18191730,0],[18191730,961],[0]],[[0,0],[0]],[[3475104774,6418519],[6418519]],[[0,0],[0]],[[2261972970,1556820],[1556820]],[[0,0],[0]],[[1135294648,246977],[246977]],[[0,0],[0]],[[437934427,23064],[23064]],[[0,0],[0]],[[128540477,961],[961]],[[0]],[[28166910]],[[0]],[[4459040]],[[0]],[[481461]],[[0]],[[31713]],[[0]],[[961]]]
theorem step084 : p084=NestedHorner.scale (-1) p081 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_scaled (-1) e084 e081 p081 p084 rfl h081 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
