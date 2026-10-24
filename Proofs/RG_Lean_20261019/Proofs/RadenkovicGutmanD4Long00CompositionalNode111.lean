/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode109
import Proofs.RadenkovicGutmanD4Long00CompositionalNode110
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e111 : NestedArithmetic.Expr 3 := .plus e109 e110
noncomputable def p111 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0,0]],[[0,0,144],[0,0,384],[144,384,32]],[[0,0,0],[0,0,0],[0,0,0]],[[1296,3456,3984],[3456,8928,1856],[3984,1856,4]],[[0,0,0],[0,0,0],[0,0]],[[71712,101088,25648],[101088,68232,3240],[25648,3240]],[[0,0,0],[0,0,0],[0,0]],[[1301076,845928,76740],[845928,218912,2592],[76740,2592]],[[0,0,0],[0,0,0],[0,0]],[[11013816,3588248,129376],[3588248,388616,976],[129376,976]],[[0,0,0],[0,0,0],[0,0]],[[54563452,9289240,133456],[9289240,422032,160],[133456,160]],[[0,0,0],[0,0,0],[0,0]],[[177997992,16023552,87408],[16023552,292000,8],[87408,8]],[[0,0,0],[0,0],[0]],[[409207508,19317720,36696],[19317720,129744],[36696]],[[0,0,0],[0,0],[0]],[[691512496,16717304,9712],[16717304,36296],[9712]],[[0,0,0],[0,0],[0]],[[882802264,10523376,1536],[10523376,6032],[1536]],[[0,0,0],[0,0],[0]],[[866746952,4832256,128],[4832256,520],[128]],[[0,0,0],[0,0],[0]],[[661798208,1606808,4],[1606808,16],[4]],[[0,0],[0]],[[395272544,379368],[379368]],[[0,0],[0]],[[184878000,61240],[61240]],[[0,0],[0]],[[67467000,6304],[6304]],[[0,0],[0]],[[19033844,360],[360]],[[0,0],[0]],[[4084304,8],[8]],[[0]],[[649160]],[[0]],[[73208]],[[0]],[[5444]],[[0]],[[232]],[[0]],[[4]]]
theorem step111 : p111=NestedHorner.add p109 p110 := by decide +kernel
#print axioms step111
theorem h111 : NestedArithmetic.compile e111=p111 := StagedExprCompile.compile_plus e111 e109 e110 p109 p110 p111 rfl h109 h110 step111
#print axioms h111
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
