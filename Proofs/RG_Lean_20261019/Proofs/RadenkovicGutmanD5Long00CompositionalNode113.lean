/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,25]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-450,450],[0,450]],[[0,0,0],[0,0,0],[0,0]],[[2025,-4050,2025],[-4050,4200,1200],[2025,1200]],[[0,0,0],[0,0,0],[0,0]],[[-1350,-9450,10800],[-9450,29950,1100],[10800,1100]],[[0,0,0],[0,0,0],[0,0]],[[-74925,68850,24300],[68850,74300,400],[24300,400]],[[0,0,0],[0,0,0],[0,0]],[[-206250,431400,30000],[431400,97800,50],[30000,50]],[[0,0,0],[0,0],[0]],[[434125,1141450,22150],[1141450,76100],[22150]],[[0,0,0],[0,0],[0]],[[4119100,1825750,10000],[1825750,35950],[10000]],[[0,0,0],[0,0],[0]],[[12869350,1952300,2700],[1952300,10100],[2700]],[[0,0,0],[0,0],[0]],[[24745350,1452800,400],[1452800,1550],[400]],[[0,0,0],[0,0],[0]],[[33304600,762650,25],[762650,100],[25]],[[0,0],[0]],[[33025800,281250],[281250]],[[0,0],[0]],[[24711800,71250],[71250]],[[0,0],[0]],[[14091250,11800],[11800]],[[0,0],[0]],[[6125925,1150],[1150]],[[0,0],[0]],[[2014100,50],[50]],[[0]],[[491950]],[[0]],[[86450]],[[0]],[[10325]],[[0]],[[750]],[[0]],[[25]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
