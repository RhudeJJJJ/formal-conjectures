/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1512 : Family 10 := level10.get ⟨336,by decide⟩
def sourceMap1512 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1512 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1512_checked : acceptsGraphIso
    (source (graph core1512) (root 10) 0 2) DegreeTwoThreeSpectrum2760.graph sourceMap1512=true := by decide +kernel
theorem fusedMap1512_checked : acceptsGraphIso
    (fused (graph core1512) (root 10) 0 2) DegreeTwoThreeSpectrum2762.graph fusedMap1512=true := by decide +kernel
theorem certified1512 : Certified (graph core1512) (root 10) 0 2 :=
  of_native_maps core1512 DegreeTwoThreeSpectrum2760.graph DegreeTwoThreeSpectrum2762.graph
    sourceMap1512 fusedMap1512 sourceMap1512_checked fusedMap1512_checked
    DegreeTwoThreeFiniteComparisons.comparison1512
#print axioms sourceMap1512_checked
#print axioms fusedMap1512_checked
#print axioms certified1512
def sourceMap1512swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1512swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1512swap_checked : acceptsGraphIso
    (source (graph core1512) (root 10) 2 0) DegreeTwoThreeSpectrum2760.graph sourceMap1512swap=true := by decide +kernel
theorem fusedMap1512swap_checked : acceptsGraphIso
    (fused (graph core1512) (root 10) 2 0) DegreeTwoThreeSpectrum2762.graph fusedMap1512swap=true := by decide +kernel
theorem certified1512swap : Certified (graph core1512) (root 10) 2 0 :=
  of_native_maps core1512 DegreeTwoThreeSpectrum2760.graph DegreeTwoThreeSpectrum2762.graph
    sourceMap1512swap fusedMap1512swap sourceMap1512swap_checked fusedMap1512swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1512
#print axioms sourceMap1512swap_checked
#print axioms fusedMap1512swap_checked
#print axioms certified1512swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
