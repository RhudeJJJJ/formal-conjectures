/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode089
import Proofs.RadenkovicGutmanD26Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4056],[0,4056,-1248]],[[0,0,0],[0,0,0],[0,0]],[[0,0,48672],[0,164268,-4732],[48672,-4732]],[[0,0,0],[0,0,0],[0,0]],[[155844,1333800,261300],[1333800,781560,-37596],[261300,-37596]],[[0,0,0],[0,0,0],[0,0]],[[11432772,11633544,534716],[11633544,1243164,-44616],[534716,-44616]],[[0,0,0],[0,0,0],[0,0]],[[124254000,44214300,456768],[44214300,279032,-18252],[456768,-18252]],[[0,0,0],[0,0,0],[0,0]],[[650205660,95652440,1924],[95652440,-1493024,-2444],[1924,-2444]],[[0,0,0],[0,0],[0]],[[2075257756,128704732,-303368],[128704732,-2058472],[-303368]],[[0,0,0],[0,0],[0]],[[4465720480,109210504,-246012],[109210504,-1257828],[-246012]],[[0,0,0],[0,0],[0]],[[6821959664,53949376,-90688],[53949376,-410072],[-90688]],[[0,0,0],[0,0],[0]],[[7600740212,8515260,-16484],[8515260,-69316],[-16484]],[[0,0,0],[0,0],[0]],[[6240653952,-7433608,-1196],[-7433608,-4784],[-1196]],[[0,0],[0]],[[3753336496,-6002620],[-6002620]],[[0,0],[0]],[[1601662920,-2150044],[-2150044]],[[0,0],[0]],[[438068228,-437060],[-437060]],[[0,0],[0]],[[44199740,-48828],[-48828]],[[0,0],[0]],[[-20000656,-2340],[-2340]],[[0]],[[-10990096]],[[0]],[[-2709460]],[[0]],[[-390780]],[[0]],[[-31876]],[[0]],[[-1144]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
