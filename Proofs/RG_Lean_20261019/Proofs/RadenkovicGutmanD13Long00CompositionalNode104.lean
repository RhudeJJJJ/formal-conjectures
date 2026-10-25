/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode092
import Proofs.RadenkovicGutmanD13Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-936,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8424,-8424,0],[-8424,-7878,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-219726,-93366,0],[-93366,-25532,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2134782,-439452,0],[-439452,-40742,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11255712,-1160250,0],[-1160250,-34268,0],[0,0]],[[0,0,0],[0,0],[0]],[[-37386518,-1911884,0],[-1911884,-14456],[0]],[[0,0,0],[0,0],[0]],[[-84501378,-2060994,0],[-2060994,-1924],[0]],[[0,0,0],[0,0],[0]],[[-135835908,-1469624,0],[-1469624,650],[0]],[[0,0,0],[0,0],[0]],[[-159266848,-673244,0],[-673244,260],[0]],[[0,0,0],[0,0],[0]],[[-137784842,-174304,0],[-174304,26],[0]],[[0,0],[0]],[[-87797476,-9074],[-9074]],[[0,0],[0]],[[-40365572,9620],[9620]],[[0,0],[0]],[[-12579320,3302],[3302]],[[0,0],[0]],[[-2109354,468],[468]],[[0,0],[0]],[[136006,26],[26]],[[0]],[[186732]],[[0]],[[53352]],[[0]],[[8242]],[[0]],[[702]],[[0]],[[26]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
