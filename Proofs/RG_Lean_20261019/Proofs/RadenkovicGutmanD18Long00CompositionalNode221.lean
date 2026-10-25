/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[648],[0],[0]],[[0,0],[0,0],[0]],[[20088,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[285768,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2472768,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[14545008,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[61569072,972,0],[972,0],[0]],[[0,0,0],[0,0],[0]],[[193693032,21708,0],[21708,0],[0]],[[0,0,0],[0,0],[0]],[[461174472,215460,0],[215460,0],[0]],[[0,0,0],[0,0],[0]],[[838423872,1252584,0],[1252584,0],[0]],[[0,0,0],[0,0],[0]],[[1165738392,4733316,0],[4733316,0],[0]],[[0,0,0],[0,0],[0]],[[1233275544,12201516,324],[12201516,648],[324]],[[0,0,0],[0,0],[0]],[[980461584,21914064,4536],[21914064,9072],[4536]],[[0,0,0],[0,0],[0]],[[573025104,27519588,26244],[27519588,52488],[26244]],[[0,0,0],[0,0],[0]],[[237432384,23886252,81000],[23886252,162000],[81000]],[[0,0,0],[0,0],[0]],[[65592504,13915800,143856],[13915800,287712],[143856]],[[0,0,0],[0,0],[0]],[[10760040,5140908,148392],[5140908,296784],[148392]],[[0,0,0],[0,0],[0]],[[787320,1076004,85860],[1076004,171720],[85860]],[[0,0,0],[0,0],[0]],[[0,96228,25272],[96228,50544],[25272]],[[0,0,0],[0,0],[0]],[[0,0,2916],[0,5832],[2916]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
