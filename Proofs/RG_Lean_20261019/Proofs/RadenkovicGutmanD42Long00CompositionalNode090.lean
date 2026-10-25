/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode035
import Proofs.RadenkovicGutmanD42Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5292],[0,-5292]],[[0,0,0],[0,0,0],[0,0]],[[0,-47628,-79380],[-47628,-254016,-23184],[-79380,-23184]],[[0,0,0],[0,0,0],[0,0]],[[-857304,-2955204,-610848],[-2955204,-1893024,-29316],[-610848,-29316]],[[0,0,0],[0,0,0],[0,0]],[[-29760696,-27683208,-1871604],[-27683208,-5616576,-13692],[-1871604,-13692]],[[0,0,0],[0,0,0],[0,0]],[[-307159776,-119557872,-2995020],[-119557872,-8748432,-2352],[-2995020,-2352]],[[0,0,0],[0,0,0],[0,0]],[[-1641052224,-301329840,-2751924],[-301329840,-7874832,-84],[-2751924,-84]],[[0,0,0],[0,0],[0]],[[-5467635432,-490281120,-1498140],[-490281120,-4228560],[-1498140]],[[0,0,0],[0,0],[0]],[[-12441073176,-542305008,-478380],[-542305008,-1341984],[-478380]],[[0,0,0],[0,0],[0]],[[-20360876928,-418795356,-83748],[-418795356,-236208],[-83748]],[[0,0,0],[0,0],[0]],[[-24737748168,-228121488,-6552],[-228121488,-19152],[-6552]],[[0,0,0],[0,0],[0]],[[-22751279376,-87320016,-84],[-87320016,-336],[-84]],[[0,0],[0]],[[-16015381536,-23030364],[-23030364]],[[0,0],[0]],[[-8666841960,-4007556],[-4007556]],[[0,0],[0]],[[-3599197392,-421092],[-421092]],[[0,0],[0]],[[-1137354792,-21756],[-21756]],[[0,0],[0]],[[-268893240,-252],[-252]],[[0]],[[-46189584]],[[0]],[[-5483688]],[[0]],[[-410760]],[[0]],[[-15960]],[[0]],[[-168]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
