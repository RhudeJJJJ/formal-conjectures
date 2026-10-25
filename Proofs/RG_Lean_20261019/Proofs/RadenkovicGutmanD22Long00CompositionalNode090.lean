/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode035
import Proofs.RadenkovicGutmanD22Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1452],[0,-1452]],[[0,0,0],[0,0,0],[0,0]],[[0,-13068,-21780],[-13068,-69696,-6424],[-21780,-6424]],[[0,0,0],[0,0,0],[0,0]],[[-235224,-811404,-168168],[-811404,-521664,-8316],[-168168,-8316]],[[0,0,0],[0,0,0],[0,0]],[[-8175816,-7618248,-517484],[-7618248,-1556896,-4092],[-517484,-4092]],[[0,0,0],[0,0,0],[0,0]],[[-84528576,-32992432,-832700],[-32992432,-2444112,-792],[-832700,-792]],[[0,0,0],[0,0,0],[0,0]],[[-452510784,-83424000,-770924],[-83424000,-2224112,-44],[-770924,-44]],[[0,0,0],[0,0],[0]],[[-1511091912,-136265360,-424380],[-136265360,-1213520],[-424380]],[[0,0,0],[0,0],[0]],[[-3447252776,-151446768,-137940],[-151446768,-394944],[-137940]],[[0,0,0],[0,0],[0]],[[-5658598528,-117663436,-24948],[-117663436,-72688],[-24948]],[[0,0,0],[0,0],[0]],[[-6899056648,-64600008,-2112],[-64600008,-6512],[-2112]],[[0,0,0],[0,0],[0]],[[-6371422816,-24994376,-44],[-24994376,-176],[-44]],[[0,0],[0]],[[-4507562576,-6694644],[-6694644]],[[0,0],[0]],[[-2454369720,-1193236],[-1193236]],[[0,0],[0]],[[-1027193552,-130812],[-130812]],[[0,0],[0]],[[-327873832,-7436],[-7436]],[[0,0],[0]],[[-78571240,-132],[-132]],[[0]],[[-13757744]],[[0]],[[-1681768]],[[0]],[[-132440]],[[0]],[[-5720]],[[0]],[[-88]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
