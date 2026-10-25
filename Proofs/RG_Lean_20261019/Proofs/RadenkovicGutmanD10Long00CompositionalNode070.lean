/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode067
import Proofs.RadenkovicGutmanD10Long00CompositionalNode069
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .plus e067 e069
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,100]],[[0,0],[0,0,0],[0,0,0]],[[0,0,900],[0,1800,2040],[900,2040,296]],[[0,0,0],[0,0,0],[0,0,0]],[[-8100,31860,21660],[31860,62688,11408],[21660,11408,4]],[[0,0,0],[0,0,0],[0,0]],[[107136,674892,142156],[674892,442952,21000],[142156,21000]],[[0,0,0],[0,0,0],[0,0]],[[4170096,5199372,434076],[5199372,1396288,16656],[434076,16656]],[[0,0,0],[0,0,0],[0,0]],[[41058240,21249280,739360],[21249280,2435136,5752],[739360,5752]],[[0,0,0],[0,0,0],[0,0]],[[214718024,53620652,761728],[53620652,2570224,736],[761728,736]],[[0,0,0],[0,0,0],[0,0]],[[716466760,90344796,491556],[90344796,1703816,8],[491556,8]],[[0,0,0],[0,0],[0]],[[1662248964,106245648,199584],[106245648,712368],[199584]],[[0,0,0],[0,0],[0]],[[2816215672,89420756,49588],[89420756,182568],[49588]],[[0,0,0],[0,0],[0]],[[3591727136,54510836,6948],[54510836,26416],[6948]],[[0,0,0],[0,0],[0]],[[3515184384,24095728,440],[24095728,1728],[440]],[[0,0,0],[0,0],[0]],[[2670686328,7645860,4],[7645860,16],[4]],[[0,0],[0]],[[1584128920,1699060],[1699060]],[[0,0],[0]],[[733940492,251980],[251980]],[[0,0],[0]],[[264336744,22680],[22680]],[[0,0],[0]],[[73203060,992],[992]],[[0,0],[0]],[[15291464,8],[8]],[[0]],[[2334380]],[[0]],[[246928]],[[0]],[[16416]],[[0]],[[552]],[[0]],[[4]]]
theorem step070 : p070=NestedHorner.add p067 p069 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_plus e070 e067 e069 p067 p069 p070 rfl h067 h069 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
