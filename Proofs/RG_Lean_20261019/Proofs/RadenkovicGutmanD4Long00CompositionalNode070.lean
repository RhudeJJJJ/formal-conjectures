/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode042
import Proofs.RadenkovicGutmanD4Long00CompositionalNode065
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .times e042 e065
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-48],[0,-48,16]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-432,-720],[-432,-2592,152],[-720,152,8]],[[0,0,0],[0,0,0],[0,0]],[[-11664,-32184,-3576],[-32184,-12240,968],[-3576,968]],[[0,0,0],[0,0,0],[0,0]],[[-405000,-279216,-4736],[-279216,-14208,1360],[-4736,1360]],[[0,0,0],[0,0,0],[0,0]],[[-4140288,-1099888,4768],[-1099888,21008,760],[4768,760]],[[0,0,0],[0,0,0],[0,0]],[[-22001544,-2480352,20760],[-2480352,75264,184],[20760,184]],[[0,0,0],[0,0,0],[0,0]],[[-73102560,-3456592,25936],[-3456592,90432,16],[25936,16]],[[0,0,0],[0,0],[0]],[[-165745544,-2958704,17048],[-2958704,58784],[17048]],[[0,0,0],[0,0],[0]],[[-268966912,-1314416,6496],[-1314416,22544],[6496]],[[0,0,0],[0,0],[0]],[[-320801424,97256,1432],[97256,5088],[1432]],[[0,0,0],[0,0],[0]],[[-284686144,544168,168],[544168,624],[168]],[[0,0,0],[0,0],[0]],[[-187788080,377928,8],[377928,32],[8]],[[0,0],[0]],[[-90321776,145616],[145616]],[[0,0],[0]],[[-29852192,35016],[35016]],[[0,0],[0]],[[-5448544,5216],[5216]],[[0,0],[0]],[[315672,440],[440]],[[0,0],[0]],[[552928,16],[16]],[[0]],[[184304]],[[0]],[[34960]],[[0]],[[4072]],[[0]],[[272]],[[0]],[[8]]]
theorem step070 : p070=NestedArithmetic.mul p042 p065 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_times e070 e042 e065 p042 p065 p070 rfl h042 h065 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
