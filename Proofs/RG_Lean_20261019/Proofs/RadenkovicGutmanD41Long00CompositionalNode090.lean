/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode035
import Proofs.RadenkovicGutmanD41Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5043],[0,-5043]],[[0,0,0],[0,0,0],[0,0]],[[0,-45387,-75645],[-45387,-242064,-22099],[-75645,-22099]],[[0,0,0],[0,0,0],[0,0]],[[-816966,-2816208,-582159],[-2816208,-1804164,-27962],[-582159,-27962]],[[0,0,0],[0,0,0],[0,0]],[[-28361340,-26382762,-1783910],[-26382762,-5353780,-13079],[-1783910,-13079]],[[0,0,0],[0,0,0],[0,0]],[[-292730652,-113949988,-2855117],[-113949988,-8340876,-2255],[-2855117,-2255]],[[0,0,0],[0,0,0],[0,0]],[[-1564046352,-287221154,-2623918],[-287221154,-7510216,-82],[-2623918,-82]],[[0,0,0],[0,0],[0]],[[-5211387246,-467374826,-1428891],[-467374826,-4034564],[-1428891]],[[0,0,0],[0,0],[0]],[[-11858835572,-517035420,-456494],[-517035420,-1281332],[-456494]],[[0,0,0],[0,0],[0]],[[-19409567936,-399346929,-79991],[-399346929,-225828],[-79991]],[[0,0,0],[0,0],[0]],[[-23584183098,-217575069,-6273],[-217575069,-18368],[-6273]],[[0,0,0],[0,0],[0]],[[-21692803898,-83307941,-82],[-83307941,-328],[-82]],[[0,0],[0]],[[-15272382658,-21981740],[-21981740]],[[0,0],[0]],[[-8266166784,-3827719],[-3827719]],[[0,0],[0]],[[-3433542868,-402702],[-402702]],[[0,0],[0]],[[-1085313050,-20869],[-20869]],[[0,0],[0]],[[-256687880,-246],[-246]],[[0]],[[-44117312]],[[0]],[[-5242178]],[[0]],[[-393272]],[[0]],[[-15334]],[[0]],[[-164]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
