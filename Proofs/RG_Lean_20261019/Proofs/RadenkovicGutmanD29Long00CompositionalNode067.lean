/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode043
import Proofs.RadenkovicGutmanD29Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,7569],[0,15138,-9396],[7569,-9396,2916]],[[0,0,0],[0,0,0],[0,0]],[[0,256041,-18966],[256041,-196854,11772],[-18966,11772]],[[0,0,0],[0,0,0],[0,0]],[[1739556,683019,-132887],[683019,-888826,89856],[-132887,89856]],[[0,0,0],[0,0,0],[0,0]],[[9598392,-2981421,9986],[-2981421,-429902,106380],[9986,106380]],[[0,0,0],[0,0,0],[0,0]],[[-11510910,-15736584,836832],[-15736584,3119892,43524],[836832,43524]],[[0,0,0],[0,0,0],[0,0]],[[-251974074,-22230989,1717498],[-22230989,6952988,5832],[1717498,5832]],[[0,0,0],[0,0],[0]],[[-1019695906,10806727,1652589],[10806727,6757614],[1652589]],[[0,0,0],[0,0],[0]],[[-2245102264,80614028,883766],[80614028,3603370],[883766]],[[0,0,0],[0,0],[0]],[[-3063047082,130523847,268789],[130523847,1089350],[268789]],[[0,0,0],[0,0],[0]],[[-2507018264,119933057,43524],[119933057,175230],[43524]],[[0,0,0],[0,0],[0]],[[-762861860,71440416,2916],[71440416,11664],[2916]],[[0,0],[0]],[[888995590,28588385],[28588385]],[[0,0],[0]],[[1481932154,7652053],[7652053]],[[0,0],[0]],[[1158002310,1316251],[1316251]],[[0,0],[0]],[[594279822,131706],[131706]],[[0,0],[0]],[[214861476,5832],[5832]],[[0]],[[55431130]],[[0]],[[10031660]],[[0]],[[1213188]],[[0]],[[88182]],[[0]],[[2916]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
