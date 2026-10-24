/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode091
import Proofs.RadenkovicGutmanD4Long00CompositionalNode102
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e103 : NestedArithmetic.Expr 3 := .plus e091 e102
noncomputable def p103 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-288,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2592,-2592,0],[-2592,-2424,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-67608,-28728,0],[-28728,-7856,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-656856,-135216,0],[-135216,-12536,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3463296,-357000,0],[-357000,-10544,0],[0,0]],[[0,0,0],[0,0],[0]],[[-11503544,-588272,0],[-588272,-4448],[0]],[[0,0,0],[0,0],[0]],[[-26000424,-634152,0],[-634152,-592],[0]],[[0,0,0],[0,0],[0]],[[-41795664,-452192,0],[-452192,200],[0]],[[0,0,0],[0,0],[0]],[[-49005184,-207152,0],[-207152,80],[0]],[[0,0,0],[0,0],[0]],[[-42395336,-53632,0],[-53632,8],[0]],[[0,0],[0]],[[-27014608,-2792],[-2792]],[[0,0],[0]],[[-12420176,2960],[2960]],[[0,0],[0]],[[-3870560,1016],[1016]],[[0,0],[0]],[[-649032,144],[144]],[[0,0],[0]],[[41848,8],[8]],[[0]],[[57456]],[[0]],[[16416]],[[0]],[[2536]],[[0]],[[216]],[[0]],[[8]]]
theorem step103 : p103=NestedHorner.add p091 p102 := by decide +kernel
#print axioms step103
theorem h103 : NestedArithmetic.compile e103=p103 := StagedExprCompile.compile_plus e103 e091 e102 p091 p102 p103 rfl h091 h102 step103
#print axioms h103
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
