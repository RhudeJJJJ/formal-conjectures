/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode034
import Proofs.RadenkovicGutmanD4Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e034 e052
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-48],[0,-48]],[[0,0,0],[0,0,0],[0,0]],[[0,-432,-432],[-432,-1728,-208],[-432,-208]],[[0,0,0],[0,0,0],[0,0]],[[-7776,-17280,-3024],[-17280,-12096,-256],[-3024,-256]],[[0,0,0],[0,0,0],[0,0]],[[-191808,-144000,-8352],[-144000,-33408,-112],[-8352,-112]],[[0,0,0],[0,0,0],[0,0]],[[-1714176,-569824,-12112],[-569824,-48448,-16],[-12112,-16]],[[0,0,0],[0,0],[0]],[[-8324928,-1331616,-10176],[-1331616,-40704],[-10176]],[[0,0,0],[0,0],[0]],[[-25746528,-2024448,-5104],[-2024448,-20416],[-5104]],[[0,0,0],[0,0],[0]],[[-55023104,-2104480,-1504],[-2104480,-6016],[-1504]],[[0,0,0],[0,0],[0]],[[-85223296,-1534032,-240],[-1534032,-960],[-240]],[[0,0,0],[0,0],[0]],[[-98515424,-790992,-16],[-790992,-64],[-16]],[[0,0],[0]],[[-86534944,-286864],[-286864]],[[0,0],[0]],[[-58336224,-71520],[-71520]],[[0,0],[0]],[[-30284800,-11664],[-11664]],[[0,0],[0]],[[-12073472,-1120],[-1120]],[[0,0],[0]],[[-3660320,-48],[-48]],[[0]],[[-828096]],[[0]],[[-135296]],[[0]],[[-15072]],[[0]],[[-1024]],[[0]],[[-32]]]
theorem step079 : p079=NestedArithmetic.mul p034 p052 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e034 e052 p034 p052 p079 rfl h034 h052 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
