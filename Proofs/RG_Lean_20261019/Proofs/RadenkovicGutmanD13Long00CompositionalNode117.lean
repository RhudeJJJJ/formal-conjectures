/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode112
import Proofs.RadenkovicGutmanD13Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,312],[0,312,536]],[[0,0,0],[0,0,0],[0,0,0]],[[0,2808,8892],[2808,11520,11312],[8892,11312,4]],[[0,0,0],[0,0,0],[0,0]],[[119232,227232,118608],[227232,266088,28816],[118608,28816]],[[0,0,0],[0,0,0],[0,0]],[[3497148,3100968,484960],[3100968,1232384,26168],[484960,26168]],[[0,0,0],[0,0,0],[0,0]],[[39246336,17070656,965344],[17070656,2639720,9584],[965344,9584]],[[0,0,0],[0,0,0],[0,0]],[[233414196,51825992,1092104],[51825992,3185712,1240],[1092104,1240]],[[0,0,0],[0,0,0],[0,0]],[[863461592,99236104,748016],[99236104,2327616,8],[748016,8]],[[0,0,0],[0,0],[0]],[[2172290068,128350040,315652],[128350040,1048176],[315652]],[[0,0,0],[0,0],[0]],[[3922901760,116368896,80288],[116368896,284392],[80288]],[[0,0,0],[0,0],[0]],[[5262689952,75340352,11348],[75340352,42832],[11348]],[[0,0,0],[0,0],[0]],[[5361760536,35001384,704],[35001384,2824],[704]],[[0,0,0],[0,0],[0]],[[4205844688,11575536,4],[11575536,16],[4]],[[0,0],[0]],[[2558594544,2661016],[2661016]],[[0,0],[0]],[[1209149432,404960],[404960]],[[0,0],[0]],[[442163592,36944],[36944]],[[0,0],[0]],[[123818996,1584],[1584]],[[0,0],[0]],[[26051104,8],[8]],[[0]],[[3987984]],[[0]],[[420424]],[[0]],[[27532]],[[0]],[[880]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
