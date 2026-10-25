/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode043
import Proofs.RadenkovicGutmanD22Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1452],[0,1452,-880]],[[0,0,0],[0,0,0],[0,0]],[[0,13068,13068],[13068,53856,-9548],[13068,-9548]],[[0,0,0],[0,0,0],[0,0]],[[320760,536976,20196],[536976,94512,-34496],[20196,-34496]],[[0,0,0],[0,0,0],[0,0]],[[7413120,3234528,-127512],[3234528,-463408,-35332],[-127512,-35332]],[[0,0,0],[0,0,0],[0,0]],[[59338224,7756936,-488972],[7756936,-1875280,-13596],[-488972,-13596]],[[0,0,0],[0,0,0],[0,0]],[[253851840,5660424,-748176],[5660424,-2914560,-1760],[-748176,-1760]],[[0,0,0],[0,0],[0]],[[676003416,-12917872,-625284],[-12917872,-2457136],[-625284]],[[0,0,0],[0,0],[0]],[[1192937504,-40491000,-306504],[-40491000,-1211760],[-306504]],[[0,0,0],[0,0],[0]],[[1405072768,-54671276,-87780],[-54671276,-348656],[-87780]],[[0,0,0],[0,0],[0]],[[1019402824,-45553772,-13596],[-45553772,-54208],[-13596]],[[0,0,0],[0,0],[0]],[[247400296,-25408108,-880],[-25408108,-3520],[-880]],[[0,0],[0]],[[-379988840,-9684840],[-9684840]],[[0,0],[0]],[[-561203456,-2495724],[-2495724]],[[0,0],[0]],[[-414751216,-416328],[-416328]],[[0,0],[0]],[[-204551160,-40612],[-40612]],[[0,0],[0]],[[-71657520,-1760],[-1760]],[[0]],[[-18008320]],[[0]],[[-3187096]],[[0]],[[-378048]],[[0]],[[-27016]],[[0]],[[-880]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
