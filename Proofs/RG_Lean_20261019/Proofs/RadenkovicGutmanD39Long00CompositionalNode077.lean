/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,13689],[0,27378],[13689]],[[0,0,0],[0,0],[0]],[[0,451737,118638],[451737,237276],[118638]],[[0,0,0],[0,0],[0]],[[3696030,5051241,403065],[5051241,806130],[403065]],[[0,0,0],[0,0],[0]],[[50512410,24133707,696618],[24133707,1393236],[696618]],[[0,0,0],[0,0],[0]],[[307920366,65326950,675324],[65326950,1350648],[675324]],[[0,0,0],[0,0],[0]],[[1114613136,112132683,380250],[112132683,760500],[380250]],[[0,0,0],[0,0],[0]],[[2690034516,129189177,123201],[129189177,246402],[123201]],[[0,0,0],[0,0],[0]],[[4602722436,102874356,21294],[102874356,42588],[21294]],[[0,0,0],[0,0],[0]],[[5789543526,57279339,1521],[57279339,3042],[1521]],[[0,0],[0]],[[5472494118,22220289],[22220289]],[[0,0],[0]],[[3935934288,5880186],[5880186]],[[0,0],[0]],[[2164957938,1011465],[1011465]],[[0,0],[0]],[[909281178,101907],[101907]],[[0,0],[0]],[[289032588,4563],[4563]],[[0]],[[68280732]],[[0]],[[11608272]],[[0]],[[1341522]],[[0]],[[94302]],[[0]],[[3042]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
