/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode095
import Proofs.RadenkovicGutmanD24Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1728,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15552,-15552,0],[-15552,-14976,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-409536,-176256,0],[-176256,-50880,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4043520,-855360,0],[-855360,-87936,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21790656,-2355840,0],[-2355840,-85248,0],[0,0]],[[0,0,0],[0,0],[0]],[[-74468928,-4118592,0],[-4118592,-48000],[0]],[[0,0,0],[0,0],[0]],[[-174619776,-4834560,0],[-4834560,-15552],[0]],[[0,0,0],[0,0],[0]],[[-294428928,-3921792,0],[-3921792,-2688],[0]],[[0,0,0],[0,0],[0]],[[-367638336,-2223360,0],[-2223360,-192],[0]],[[0,0,0],[0,0],[0]],[[-346281600,-877632,0],[-877632,0],[0]],[[0,0],[0]],[[-248658048,-236160],[-236160]],[[0,0],[0]],[[-136685568,-41280],[-41280]],[[0,0],[0]],[[-57394752,-4224],[-4224]],[[0,0],[0]],[[-18242880,-192],[-192]],[[0,0],[0]],[[-4309632,0],[0]],[[0]],[[-732672]],[[0]],[[-84672]],[[0]],[[-5952]],[[0]],[[-192]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
