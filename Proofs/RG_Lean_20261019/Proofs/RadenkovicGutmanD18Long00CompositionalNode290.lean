/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode289
import Proofs.RadenkovicGutmanD18Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[1296,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[38880,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[535248,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[4481568,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[25502688,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[104413536,1296,0],[1296,0],[0]],[[0,0,0],[0,0],[0]],[[317627568,28512,0],[28512,0],[0]],[[0,0,0],[0,0],[0]],[[731102112,278640,0],[278640,0],[0]],[[0,0,0],[0,0],[0]],[[1284753312,1594080,0],[1594080,0],[0]],[[0,0,0],[0,0],[0]],[[1726637472,5924016,0],[5924016,0],[0]],[[0,0,0],[0,0],[0]],[[1766047536,15007680,324],[15007680,648],[324]],[[0,0,0],[0,0],[0]],[[1358132832,26472096,4536],[26472096,9072],[4536]],[[0,0,0],[0,0],[0]],[[768494304,32633280,26244],[32633280,52488],[26244]],[[0,0,0],[0,0],[0]],[[308699424,27800496,81000],[27800496,162000],[81000]],[[0,0,0],[0,0],[0]],[[82826064,15901920,143856],[15901920,287712],[143856]],[[0,0,0],[0,0],[0]],[[13226976,5773680,148392],[5773680,296784],[148392]],[[0,0,0],[0,0],[0]],[[944784,1189728,85860],[1189728,171720],[85860]],[[0,0,0],[0,0],[0]],[[0,104976,25272],[104976,50544],[25272]],[[0,0,0],[0,0],[0]],[[0,0,2916],[0,5832],[2916]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
