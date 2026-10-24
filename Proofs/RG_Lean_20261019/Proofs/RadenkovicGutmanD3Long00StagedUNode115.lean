/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode110
import Proofs.RadenkovicGutmanD3Long00StagedUNode114
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e110 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,72],[0,72,16]],[[0,0,0],[0,0,0],[0,0,0]],[[0,648,972],[648,2880,672],[972,672,4]],[[0,0,0],[0,0,0],[0,0]],[[18792,34992,9288],[34992,28488,1536],[9288,1536]],[[0,0,0],[0,0,0],[0,0]],[[499068,361368,33840],[361368,106304,1448],[33840,1448]],[[0,0,0],[0,0,0],[0,0]],[[4991976,1733856,64464],[1733856,208680,624],[64464,624]],[[0,0,0],[0,0,0],[0,0]],[[27339636,4879272,72504],[4879272,243952,120],[72504,120]],[[0,0,0],[0,0,0],[0,0]],[[95544832,8947304,50896],[8947304,179136,8],[50896,8]],[[0,0,0],[0,0],[0]],[[231103988,11312200,22772],[11312200,84016],[22772]],[[0,0,0],[0,0],[0]],[[406231760,10180176,6448],[10180176,24872],[6448]],[[0,0,0],[0,0],[0]],[[535347872,6631392,1108],[6631392,4432],[1108]],[[0,0,0],[0,0],[0]],[[539774456,3144264,104],[3144264,424],[104]],[[0,0,0],[0,0],[0]],[[421779888,1080016,4],[1080016,16],[4]],[[0,0],[0]],[[257253264,264296],[264296]],[[0,0],[0]],[[122743992,44560],[44560]],[[0,0],[0]],[[45694512,4864],[4864]],[[0,0],[0]],[[13166356,304],[304]],[[0,0],[0]],[[2893104,8],[8]],[[0]],[[473104]],[[0]],[[55344]],[[0]],[[4332]],[[0]],[[200]],[[0]],[[4]]]
theorem step115 : p115=NestedHorner.add p110 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := by
  change NestedHorner.add (NestedArithmetic.compile e110) (NestedArithmetic.compile e114)=p115
  rw [h110,h114]
  exact step115.symm
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
