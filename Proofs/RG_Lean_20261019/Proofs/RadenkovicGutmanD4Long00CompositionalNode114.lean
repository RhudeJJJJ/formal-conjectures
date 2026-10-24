/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode112
import Proofs.RadenkovicGutmanD4Long00CompositionalNode113
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .plus e112 e113
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0]],[[0,0,144],[0,0,288],[144,288]],[[0,0,0],[0,0,0],[0,0]],[[1296,2592,2544],[2592,5184,768],[2544,768]],[[0,0,0],[0,0,0],[0,0]],[[45792,52704,11152],[52704,27648,704],[11152,704]],[[0,0,0],[0,0,0],[0,0]],[[605232,329184,22880],[329184,62208,256],[22880,256]],[[0,0,0],[0,0,0],[0,0]],[[3958176,1061376,26304],[1061376,76800,32],[26304,32]],[[0,0,0],[0,0],[0]],[[15522256,2103392,18176],[2103392,56704],[18176]],[[0,0,0],[0,0],[0]],[[40586560,2780000,7696],[2780000,25600],[7696]],[[0,0,0],[0,0],[0]],[[75304672,2556736,1952],[2556736,6912],[1952]],[[0,0,0],[0,0],[0]],[[103049248,1670912,272],[1670912,1024],[272]],[[0,0,0],[0,0],[0]],[[106580992,780640,16],[780640,64],[16]],[[0,0],[0]],[[84581120,258720],[258720]],[[0,0],[0]],[[51919360,59360],[59360]],[[0,0],[0]],[[24703712,8960],[8960]],[[0,0],[0]],[[9076816,800],[800]],[[0,0],[0]],[[2548416,32],[32]],[[0]],[[536160]],[[0]],[[81760]],[[0]],[[8528]],[[0]],[[544]],[[0]],[[16]]]
theorem step114 : p114=NestedHorner.add p112 p113 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_plus e114 e112 e113 p112 p113 p114 rfl h112 h113 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
