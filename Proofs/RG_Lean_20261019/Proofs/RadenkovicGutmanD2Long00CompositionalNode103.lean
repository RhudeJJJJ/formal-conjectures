/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode100
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e103 : NestedArithmetic.Expr 3 := .scaled (-1) e100
noncomputable def p103 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-4]],[[0,0],[0,0,0],[0,0,0]],[[0,0,36],[0,72,-96],[36,-96,-4]],[[0,0,0],[0,0,0],[0,0]],[[324,1404,-228],[1404,-1608,-368],[-228,-368]],[[0,0,0],[0,0,0],[0,0]],[[17604,3780,-2504],[3780,-12760,-496],[-2504,-496]],[[0,0,0],[0,0,0],[0,0]],[[142020,-37116,-7960],[-37116,-37624,-296],[-7960,-296]],[[0,0,0],[0,0,0],[0,0]],[[397164,-264512,-12968],[-264512,-59088,-80],[-12968,-80]],[[0,0,0],[0,0,0],[0,0]],[[-272420,-797204,-12432],[-797204,-55280,-8],[-12432,-8]],[[0,0,0],[0,0],[0]],[[-5292100,-1439356,-7372],[-1439356,-32136],[-7372]],[[0,0,0],[0,0],[0]],[[-18525656,-1727384,-2728],[-1727384,-11672],[-2728]],[[0,0,0],[0,0],[0]],[[-38115184,-1442076,-612],[-1442076,-2568],[-612]],[[0,0,0],[0,0],[0]],[[-53979792,-854580,-76],[-854580,-312],[-76]],[[0,0,0],[0,0],[0]],[[-55845664,-361104,-4],[-361104,-16],[-4]],[[0,0],[0]],[[-43435080,-107780],[-107780]],[[0,0],[0]],[[-25759736,-22132],[-22132]],[[0,0],[0]],[[-11707428,-2964],[-2964]],[[0,0],[0]],[[-4067396,-232],[-232]],[[0,0],[0]],[[-1069224,-8],[-8]],[[0]],[[-208480]],[[0]],[[-29132]],[[0]],[[-2748]],[[0]],[[-156]],[[0]],[[-4]]]
theorem step103 : p103=NestedHorner.scale (-1) p100 := by decide +kernel
#print axioms step103
theorem h103 : NestedArithmetic.compile e103=p103 := StagedExprCompile.compile_scaled (-1) e103 e100 p100 p103 rfl h100 step103
#print axioms h103
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
