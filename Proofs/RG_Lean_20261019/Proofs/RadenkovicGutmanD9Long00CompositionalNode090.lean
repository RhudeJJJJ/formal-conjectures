/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode035
import Proofs.RadenkovicGutmanD9Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-243],[0,-243]],[[0,0,0],[0,0,0],[0,0]],[[0,-2187,-3645],[-2187,-11664,-1107],[-3645,-1107]],[[0,0,0],[0,0,0],[0,0]],[[-39366,-136080,-28431],[-136080,-88452,-1530],[-28431,-1530]],[[0,0,0],[0,0,0],[0,0]],[[-1373436,-1286442,-88614],[-1286442,-268596,-855],[-88614,-855]],[[0,0,0],[0,0,0],[0,0]],[[-14273820,-5617188,-144909],[-5617188,-431244,-207],[-144909,-207]],[[0,0,0],[0,0,0],[0,0]],[[-76869648,-14340258,-137070],[-14340258,-404424,-18],[-137070,-18]],[[0,0,0],[0,0],[0]],[[-258423534,-23689962,-77787],[-23689962,-230148],[-77787]],[[0,0,0],[0,0],[0]],[[-594031860,-26691228,-26478],[-26691228,-79668],[-26478]],[[0,0,0],[0,0],[0]],[[-983574720,-21090609,-5175],[-21090609,-16164],[-5175]],[[0,0,0],[0,0],[0]],[[-1211248314,-11830941,-513],[-11830941,-1728],[-513]],[[0,0,0],[0,0],[0]],[[-1131782202,-4708773,-18],[-4708773,-72],[-18]],[[0,0],[0]],[[-811890882,-1311084],[-1311084]],[[0,0],[0]],[[-449532288,-247239],[-247239]],[[0,0],[0]],[[-192038868,-29646],[-29646]],[[0,0],[0]],[[-62897562,-1989],[-1989]],[[0,0],[0]],[[-15582600,-54],[-54]],[[0]],[[-2852928]],[[0]],[[-371394]],[[0]],[[-32184]],[[0]],[[-1638]],[[0]],[[-36]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
