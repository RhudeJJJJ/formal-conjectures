/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode221
import Proofs.RadenkovicGutmanD18Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[648,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[20088,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[285768,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2472768,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[14545008,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[61569072,972,0],[972,0],[0]],[[0,0,0],[0,0],[0]],[[193693032,21708,0],[21708,0],[0]],[[0,0,0],[0,0],[0]],[[461174472,215460,0],[215460,0],[0]],[[0,0,0],[0,0],[0]],[[838423872,1252584,0],[1252584,0],[0]],[[0,0,0],[0,0],[0]],[[1165738392,4733316,0],[4733316,0],[0]],[[0,0,0],[0,0],[0]],[[1233275544,12201516,324],[12201516,648],[324]],[[0,0,0],[0,0],[0]],[[980461584,21914064,4536],[21914064,9072],[4536]],[[0,0,0],[0,0],[0]],[[573025104,27519588,26244],[27519588,52488],[26244]],[[0,0,0],[0,0],[0]],[[237432384,23886252,81000],[23886252,162000],[81000]],[[0,0,0],[0,0],[0]],[[65592504,13915800,143856],[13915800,287712],[143856]],[[0,0,0],[0,0],[0]],[[10760040,5140908,148392],[5140908,296784],[148392]],[[0,0,0],[0,0],[0]],[[787320,1076004,85860],[1076004,171720],[85860]],[[0,0,0],[0,0],[0]],[[0,96228,25272],[96228,50544],[25272]],[[0,0,0],[0,0],[0]],[[0,0,2916],[0,5832],[2916]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
