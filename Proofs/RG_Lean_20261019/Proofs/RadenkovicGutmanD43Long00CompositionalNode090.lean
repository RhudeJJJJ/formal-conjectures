/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode035
import Proofs.RadenkovicGutmanD43Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5547],[0,-5547]],[[0,0,0],[0,0,0],[0,0]],[[0,-49923,-83205],[-49923,-266256,-24295],[-83205,-24295]],[[0,0,0],[0,0,0],[0,0]],[[-898614,-3097548,-640227],[-3097548,-1984020,-30702],[-640227,-30702]],[[0,0,0],[0,0,0],[0,0]],[[-31193748,-29014938,-1961402],[-29014938,-5885668,-14319],[-1961402,-14319]],[[0,0,0],[0,0,0],[0,0]],[[-321936012,-125300452,-3138269],[-125300452,-9165708,-2451],[-3138269,-2451]],[[0,0,0],[0,0,0],[0,0]],[[-1719908496,-315776778,-2882978],[-315776778,-8248088,-86],[-2882978,-86]],[[0,0,0],[0,0],[0]],[[-5730033198,-513735362,-1569027],[-513735362,-4427108],[-1569027]],[[0,0,0],[0,0],[0]],[[-13037263052,-568177404,-500778],[-568177404,-1404036],[-500778]],[[0,0,0],[0,0],[0]],[[-21334943296,-438706081,-87591],[-438706081,-246820],[-87591]],[[0,0,0],[0,0],[0]],[[-25918853290,-238917417,-6837],[-238917417,-19952],[-6837]],[[0,0,0],[0,0],[0]],[[-23834963554,-91426385,-86],[-91426385,-344],[-86]],[[0,0],[0]],[[-16776023354,-24103392],[-24103392]],[[0,0],[0]],[[-9076996248,-4191511],[-4191511]],[[0,0],[0]],[[-3768752372,-439890],[-439890]],[[0,0],[0]],[[-1190614186,-22661],[-22661]],[[0,0],[0]],[[-281381680,-258],[-258]],[[0]],[[-48309296]],[[0]],[[-5730610]],[[0]],[[-428624]],[[0]],[[-16598]],[[0]],[[-172]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
