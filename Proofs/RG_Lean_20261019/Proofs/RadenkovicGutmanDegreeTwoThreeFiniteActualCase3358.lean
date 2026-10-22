/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3358 : Family 9 := level9.get ⟨395,by decide⟩
def sourceMap3358 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3358 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3358_checked : acceptsGraphIso
    (source (graph core3358) (root 9) 0 5) DegreeTwoThreeSpectrum6374.graph sourceMap3358=true := by decide +kernel
theorem fusedMap3358_checked : acceptsGraphIso
    (fused (graph core3358) (root 9) 0 5) DegreeTwoThreeSpectrum5316.graph fusedMap3358=true := by decide +kernel
theorem certified3358 : Certified (graph core3358) (root 9) 0 5 :=
  of_native_maps core3358 DegreeTwoThreeSpectrum6374.graph DegreeTwoThreeSpectrum5316.graph
    sourceMap3358 fusedMap3358 sourceMap3358_checked fusedMap3358_checked
    DegreeTwoThreeFiniteComparisons.comparison3358
#print axioms sourceMap3358_checked
#print axioms fusedMap3358_checked
#print axioms certified3358
def sourceMap3358swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3358swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3358swap_checked : acceptsGraphIso
    (source (graph core3358) (root 9) 5 0) DegreeTwoThreeSpectrum6374.graph sourceMap3358swap=true := by decide +kernel
theorem fusedMap3358swap_checked : acceptsGraphIso
    (fused (graph core3358) (root 9) 5 0) DegreeTwoThreeSpectrum5316.graph fusedMap3358swap=true := by decide +kernel
theorem certified3358swap : Certified (graph core3358) (root 9) 5 0 :=
  of_native_maps core3358 DegreeTwoThreeSpectrum6374.graph DegreeTwoThreeSpectrum5316.graph
    sourceMap3358swap fusedMap3358swap sourceMap3358swap_checked fusedMap3358swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3358
#print axioms sourceMap3358swap_checked
#print axioms fusedMap3358swap_checked
#print axioms certified3358swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
