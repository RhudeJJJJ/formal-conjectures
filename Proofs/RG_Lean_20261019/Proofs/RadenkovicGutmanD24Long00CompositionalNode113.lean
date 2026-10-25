/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,576]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-10368,10368],[0,10368]],[[0,0,0],[0,0,0],[0,0]],[[46656,-93312,46656],[-93312,96768,27648],[46656,27648]],[[0,0,0],[0,0,0],[0,0]],[[-31104,-217728,248832],[-217728,690048,25344],[248832,25344]],[[0,0,0],[0,0,0],[0,0]],[[-1726272,1586304,559872],[1586304,1711872,9216],[559872,9216]],[[0,0,0],[0,0,0],[0,0]],[[-4752000,9939456,691200],[9939456,2253312,1152],[691200,1152]],[[0,0,0],[0,0],[0]],[[10002240,26299008,510336],[26299008,1753344],[510336]],[[0,0,0],[0,0],[0]],[[94904064,42065280,230400],[42065280,828288],[230400]],[[0,0,0],[0,0],[0]],[[296509824,44980992,62208],[44980992,232704],[62208]],[[0,0,0],[0,0],[0]],[[570132864,33472512,9216],[33472512,35712],[9216]],[[0,0,0],[0,0],[0]],[[767337984,17571456,576],[17571456,2304],[576]],[[0,0],[0]],[[760914432,6480000],[6480000]],[[0,0],[0]],[[569359872,1641600],[1641600]],[[0,0],[0]],[[324662400,271872],[271872]],[[0,0],[0]],[[141141312,26496],[26496]],[[0,0],[0]],[[46404864,1152],[1152]],[[0]],[[11334528]],[[0]],[[1991808]],[[0]],[[237888]],[[0]],[[17280]],[[0]],[[576]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
