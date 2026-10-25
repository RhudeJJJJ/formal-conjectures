/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode035
import Proofs.RadenkovicGutmanD38Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4332],[0,-4332]],[[0,0,0],[0,0,0],[0,0]],[[0,-38988,-38988],[-38988,-155952,-18772],[-38988,-18772]],[[0,0,0],[0,0,0],[0,0]],[[-701784,-1559520,-272916],[-1559520,-1091664,-23104],[-272916,-23104]],[[0,0,0],[0,0,0],[0,0]],[[-17310672,-12996000,-753768],[-12996000,-3015072,-10108],[-753768,-10108]],[[0,0,0],[0,0,0],[0,0]],[[-154704384,-51426616,-1093108],[-51426616,-4372432,-1444],[-1093108,-1444]],[[0,0,0],[0,0],[0]],[[-751324752,-120178344,-918384],[-120178344,-3673536],[-918384]],[[0,0,0],[0,0],[0]],[[-2323624152,-182706432,-460636],[-182706432,-1842544],[-460636]],[[0,0,0],[0,0],[0]],[[-4965835136,-189929320,-135736],[-189929320,-542944],[-135736]],[[0,0,0],[0,0],[0]],[[-7691402464,-138446388,-21660],[-138446388,-86640],[-21660]],[[0,0,0],[0,0],[0]],[[-8891017016,-71387028,-1444],[-71387028,-5776],[-1444]],[[0,0],[0]],[[-7809778696,-25889476],[-25889476]],[[0,0],[0]],[[-5264844216,-6454680],[-6454680]],[[0,0],[0]],[[-2733203200,-1052676],[-1052676]],[[0,0],[0]],[[-1089630848,-101080],[-101080]],[[0,0],[0]],[[-330343880,-4332],[-4332]],[[0]],[[-74735664]],[[0]],[[-12210464]],[[0]],[[-1360248]],[[0]],[[-92416]],[[0]],[[-2888]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
