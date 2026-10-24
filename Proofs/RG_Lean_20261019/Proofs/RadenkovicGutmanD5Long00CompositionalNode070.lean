/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode067
import Proofs.RadenkovicGutmanD5Long00CompositionalNode069
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .plus e067 e069
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,25]],[[0,0],[0,0,0],[0,0,0]],[[0,0,225],[0,450,570],[225,570,56]],[[0,0,0],[0,0,0],[0,0,0]],[[-2025,8505,5955],[8505,17688,2848],[5955,2848,4]],[[0,0,0],[0,0,0],[0,0]],[[36666,189567,38401],[189567,120902,5020],[38401,5020]],[[0,0,0],[0,0,0],[0,0]],[[1282581,1460187,115206],[1460187,371268,3976],[115206,3976]],[[0,0,0],[0,0,0],[0,0]],[[12374610,5924070,194220],[5924070,637916,1442],[194220,1442]],[[0,0,0],[0,0,0],[0,0]],[[63948179,14850487,199608],[14850487,670324,216],[199608,216]],[[0,0,0],[0,0,0],[0,0]],[[211607880,24920291,129641],[24920291,447186,8],[129641,8]],[[0,0,0],[0,0],[0]],[[488085794,29278548,53614],[29278548,190668],[53614]],[[0,0,0],[0,0],[0]],[[823829042,24704971,13833],[24704971,50838],[13833]],[[0,0,0],[0,0],[0]],[[1048755226,15160941,2093],[15160941,7956],[2093]],[[0,0,0],[0,0],[0]],[[1026450344,6781948,160],[6781948,628],[160]],[[0,0,0],[0,0],[0]],[[781457098,2193645,4],[2193645,16],[4]],[[0,0],[0]],[[465545330,502475],[502475]],[[0,0],[0]],[[217235747,78315],[78315]],[[0,0],[0]],[[79082944,7710],[7710]],[[0,0],[0]],[[22244990,412],[412]],[[0,0],[0]],[[4753614,8],[8]],[[0]],[[750765]],[[0]],[[83798]],[[0]],[[6121]],[[0]],[[252]],[[0]],[[4]]]
theorem step070 : p070=NestedHorner.add p067 p069 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_plus e070 e067 e069 p067 p069 p070 rfl h067 h069 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
