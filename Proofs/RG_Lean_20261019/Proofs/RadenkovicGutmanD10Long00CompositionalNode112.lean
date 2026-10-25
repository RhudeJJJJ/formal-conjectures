/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode110
import Proofs.RadenkovicGutmanD10Long00CompositionalNode111
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .plus e110 e111
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,100]],[[0,0],[0,0,0],[0,0,0]],[[0,0,900],[0,0,2040],[900,2040,296]],[[0,0,0],[0,0,0],[0,0,0]],[[8100,18360,21660],[18360,41328,11408],[21660,11408,4]],[[0,0,0],[0,0,0],[0,0]],[[368496,485352,142156],[485352,340392,21000],[142156,21000]],[[0,0,0],[0,0,0],[0,0]],[[6140016,4059792,434076],[4059792,1138208,16656],[434076,16656]],[[0,0,0],[0,0,0],[0,0]],[[50531160,17375000,739360],[17375000,2063816,5752],[739360,5752]],[[0,0,0],[0,0,0],[0,0]],[[247825504,45315952,761728],[45315952,2254384,736],[761728,736]],[[0,0,0],[0,0,0],[0,0]],[[805260720,78481656,491556],[78481656,1545376,8],[491556,8]],[[0,0,0],[0,0],[0]],[[1847509004,94623288,199584],[94623288,667728],[199584]],[[0,0,0],[0,0],[0]],[[3116609032,81532616,49588],[81532616,176648],[49588]],[[0,0,0],[0,0],[0]],[[3969609976,50834376,6948],[50834376,26336],[6948]],[[0,0,0],[0,0],[0]],[[3884246504,22962888,440],[22962888,1768],[440]],[[0,0,0],[0,0],[0]],[[2951070368,7439600,4],[7439600,16],[4]],[[0,0],[0]],[[1750013720,1686360],[1686360]],[[0,0],[0]],[[810263412,254800],[254800]],[[0,0],[0]],[[291497184,23320],[23320]],[[0,0],[0]],[[80595020,1032],[1032]],[[0,0],[0]],[[16799864,8],[8]],[[0]],[[2557580]],[[0]],[[269528]],[[0]],[[17816]],[[0]],[[592]],[[0]],[[4]]]
theorem step112 : p112=NestedHorner.add p110 p111 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_plus e112 e110 e111 p110 p111 p112 rfl h110 h111 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
