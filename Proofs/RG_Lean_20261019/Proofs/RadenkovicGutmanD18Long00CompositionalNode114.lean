/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,2916],[0,5832],[2916]],[[0,0,0],[0,0],[0]],[[0,104976,25272],[104976,50544],[25272]],[[0,0,0],[0,0],[0]],[[944784,1189728,85860],[1189728,171720],[85860]],[[0,0,0],[0,0],[0]],[[13226976,5773680,148392],[5773680,296784],[148392]],[[0,0,0],[0,0],[0]],[[82826064,15901920,143856],[15901920,287712],[143856]],[[0,0,0],[0,0],[0]],[[308699424,27800496,81000],[27800496,162000],[81000]],[[0,0,0],[0,0],[0]],[[768494304,32633280,26244],[32633280,52488],[26244]],[[0,0,0],[0,0],[0]],[[1358132832,26472096,4536],[26472096,9072],[4536]],[[0,0,0],[0,0],[0]],[[1766047536,15007680,324],[15007680,648],[324]],[[0,0],[0]],[[1726637472,5924016],[5924016]],[[0,0],[0]],[[1284753312,1594080],[1594080]],[[0,0],[0]],[[731102112,278640],[278640]],[[0,0],[0]],[[317627568,28512],[28512]],[[0,0],[0]],[[104413536,1296],[1296]],[[0]],[[25502688]],[[0]],[[4481568]],[[0]],[[535248]],[[0]],[[38880]],[[0]],[[1296]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
