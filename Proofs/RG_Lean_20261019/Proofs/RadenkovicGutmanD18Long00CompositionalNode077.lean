/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,2916],[0,5832],[2916]],[[0,0,0],[0,0],[0]],[[0,96228,25272],[96228,50544],[25272]],[[0,0,0],[0,0],[0]],[[787320,1076004,85860],[1076004,171720],[85860]],[[0,0,0],[0,0],[0]],[[10760040,5140908,148392],[5140908,296784],[148392]],[[0,0,0],[0,0],[0]],[[65592504,13915800,143856],[13915800,287712],[143856]],[[0,0,0],[0,0],[0]],[[237432384,23886252,81000],[23886252,162000],[81000]],[[0,0,0],[0,0],[0]],[[573025104,27519588,26244],[27519588,52488],[26244]],[[0,0,0],[0,0],[0]],[[980461584,21914064,4536],[21914064,9072],[4536]],[[0,0,0],[0,0],[0]],[[1233275544,12201516,324],[12201516,648],[324]],[[0,0],[0]],[[1165738392,4733316],[4733316]],[[0,0],[0]],[[838423872,1252584],[1252584]],[[0,0],[0]],[[461174472,215460],[215460]],[[0,0],[0]],[[193693032,21708],[21708]],[[0,0],[0]],[[61569072,972],[972]],[[0]],[[14545008]],[[0]],[[2472768]],[[0]],[[285768]],[[0]],[[20088]],[[0]],[[648]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
