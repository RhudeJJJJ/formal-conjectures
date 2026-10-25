/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode035
import Proofs.RadenkovicGutmanD10Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-300],[0,-300]],[[0,0,0],[0,0,0],[0,0]],[[0,-2700,-4500],[-2700,-14400,-1360],[-4500,-1360]],[[0,0,0],[0,0,0],[0,0]],[[-48600,-167940,-35040],[-167940,-108960,-1860],[-35040,-1860]],[[0,0,0],[0,0,0],[0,0]],[[-1694520,-1585800,-108980],[-1585800,-329920,-1020],[-108980,-1020]],[[0,0,0],[0,0,0],[0,0]],[[-17595360,-6914800,-177740],[-6914800,-527760,-240],[-177740,-240]],[[0,0,0],[0,0,0],[0,0]],[[-94662720,-17624880,-167540],[-17624880,-492560,-20],[-167540,-20]],[[0,0,0],[0,0],[0]],[[-317885160,-29061920,-94620],[-29061920,-278480],[-94620]],[[0,0,0],[0,0],[0]],[[-729796760,-32670960,-31980],[-32670960,-95520],[-31980]],[[0,0,0],[0,0],[0]],[[-1206647680,-25745500,-6180],[-25745500,-19120],[-6180]],[[0,0,0],[0,0],[0]],[[-1483531720,-14393040,-600],[-14393040,-2000],[-600]],[[0,0,0],[0,0],[0]],[[-1383579280,-5703440,-20],[-5703440,-80],[-20]],[[0,0],[0]],[[-990315680,-1578780],[-1578780]],[[0,0],[0]],[[-546875880,-295300],[-295300]],[[0,0],[0]],[[-232878800,-34980],[-34980]],[[0,0],[0]],[[-75974440,-2300],[-2300]],[[0,0],[0]],[[-18729400,-60],[-60]],[[0]],[[-3407120]],[[0]],[[-439720]],[[0]],[[-37640]],[[0]],[[-1880]],[[0]],[[-40]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
