/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3073 : Family 10 := level10.get ⟨1804,by decide⟩
def sourceMap3073 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3073 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3073_checked : acceptsGraphIso
    (source (graph core3073) (root 10) 0 4) DegreeTwoThreeSpectrum7063.graph sourceMap3073=true := by decide +kernel
theorem fusedMap3073_checked : acceptsGraphIso
    (fused (graph core3073) (root 10) 0 4) DegreeTwoThreeSpectrum7064.graph fusedMap3073=true := by decide +kernel
theorem certified3073 : Certified (graph core3073) (root 10) 0 4 :=
  of_native_maps core3073 DegreeTwoThreeSpectrum7063.graph DegreeTwoThreeSpectrum7064.graph
    sourceMap3073 fusedMap3073 sourceMap3073_checked fusedMap3073_checked
    DegreeTwoThreeFiniteComparisons.comparison3073
#print axioms sourceMap3073_checked
#print axioms fusedMap3073_checked
#print axioms certified3073
def sourceMap3073swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3073swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3073swap_checked : acceptsGraphIso
    (source (graph core3073) (root 10) 4 0) DegreeTwoThreeSpectrum7063.graph sourceMap3073swap=true := by decide +kernel
theorem fusedMap3073swap_checked : acceptsGraphIso
    (fused (graph core3073) (root 10) 4 0) DegreeTwoThreeSpectrum7064.graph fusedMap3073swap=true := by decide +kernel
theorem certified3073swap : Certified (graph core3073) (root 10) 4 0 :=
  of_native_maps core3073 DegreeTwoThreeSpectrum7063.graph DegreeTwoThreeSpectrum7064.graph
    sourceMap3073swap fusedMap3073swap sourceMap3073swap_checked fusedMap3073swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3073
#print axioms sourceMap3073swap_checked
#print axioms fusedMap3073swap_checked
#print axioms certified3073swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
