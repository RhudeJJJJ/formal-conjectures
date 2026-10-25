/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,324]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-5832,5832],[0,5832]],[[0,0,0],[0,0,0],[0,0]],[[26244,-52488,26244],[-52488,54432,15552],[26244,15552]],[[0,0,0],[0,0,0],[0,0]],[[-17496,-122472,139968],[-122472,388152,14256],[139968,14256]],[[0,0,0],[0,0,0],[0,0]],[[-971028,892296,314928],[892296,962928,5184],[314928,5184]],[[0,0,0],[0,0,0],[0,0]],[[-2673000,5590944,388800],[5590944,1267488,648],[388800,648]],[[0,0,0],[0,0],[0]],[[5626260,14793192,287064],[14793192,986256],[287064]],[[0,0,0],[0,0],[0]],[[53383536,23661720,129600],[23661720,465912],[129600]],[[0,0,0],[0,0],[0]],[[166786776,25301808,34992],[25301808,130896],[34992]],[[0,0,0],[0,0],[0]],[[320699736,18828288,5184],[18828288,20088],[5184]],[[0,0,0],[0,0],[0]],[[431627616,9883944,324],[9883944,1296],[324]],[[0,0],[0]],[[428014368,3645000],[3645000]],[[0,0],[0]],[[320264928,923400],[923400]],[[0,0],[0]],[[182622600,152928],[152928]],[[0,0],[0]],[[79391988,14904],[14904]],[[0,0],[0]],[[26102736,648],[648]],[[0]],[[6375672]],[[0]],[[1120392]],[[0]],[[133812]],[[0]],[[9720]],[[0]],[[324]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
