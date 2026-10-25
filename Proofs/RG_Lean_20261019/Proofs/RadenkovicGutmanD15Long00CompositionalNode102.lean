/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode100
import Proofs.RadenkovicGutmanD15Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,225]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-2025],[0,-4050,6570],[-2025,6570,30]],[[0,0,0],[0,0,0],[0,0]],[[-18225,-68445,23355],[-68445,125550,22260],[23355,22260]],[[0,0,0],[0,0,0],[0,0]],[[-848070,145395,198765],[145395,888570,24780],[198765,24780]],[[0,0,0],[0,0,0],[0,0]],[[-4703265,4597425,567090],[4597425,2387010,10800],[567090,10800]],[[0,0,0],[0,0,0],[0,0]],[[3852900,23018880,835140],[23018880,3389220,1770],[835140,1770]],[[0,0,0],[0,0,0],[0,0]],[[125741205,59580045,713340],[59580045,2819340,60],[713340,60]],[[0,0,0],[0,0],[0]],[[584809740,96308715,366315],[96308715,1419210],[366315]],[[0,0,0],[0,0],[0]],[[1533911190,104760600,112110],[104760600,428010],[112110]],[[0,0,0],[0,0],[0]],[[2705462490,79382445,19215],[79382445,72690],[19215]],[[0,0,0],[0,0],[0]],[[3434998680,42470115,1545],[42470115,5850],[1545]],[[0,0,0],[0,0],[0]],[[3248267520,16007670,30],[16007670,120],[30]],[[0,0],[0]],[[2329249650,4173075],[4173075]],[[0,0],[0]],[[1276767390,721935],[721935]],[[0,0],[0]],[[535174125,76245],[76245]],[[0,0],[0]],[[170331780,4080],[4080]],[[0,0],[0]],[[40515930,60],[60]],[[0]],[[7002150]],[[0]],[[837615]],[[0]],[[63510]],[[0]],[[2535]],[[0]],[[30]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
