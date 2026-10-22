/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1491 : Family 10 := level10.get ⟨263,by decide⟩
def sourceMap1491 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1491 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1491_checked : acceptsGraphIso
    (source (graph core1491) (root 10) 0 2) DegreeTwoThreeSpectrum2612.graph sourceMap1491=true := by decide +kernel
theorem fusedMap1491_checked : acceptsGraphIso
    (fused (graph core1491) (root 10) 0 2) DegreeTwoThreeSpectrum2614.graph fusedMap1491=true := by decide +kernel
theorem certified1491 : Certified (graph core1491) (root 10) 0 2 :=
  of_native_maps core1491 DegreeTwoThreeSpectrum2612.graph DegreeTwoThreeSpectrum2614.graph
    sourceMap1491 fusedMap1491 sourceMap1491_checked fusedMap1491_checked
    DegreeTwoThreeFiniteComparisons.comparison1491
#print axioms sourceMap1491_checked
#print axioms fusedMap1491_checked
#print axioms certified1491
def sourceMap1491swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1491swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1491swap_checked : acceptsGraphIso
    (source (graph core1491) (root 10) 2 0) DegreeTwoThreeSpectrum2612.graph sourceMap1491swap=true := by decide +kernel
theorem fusedMap1491swap_checked : acceptsGraphIso
    (fused (graph core1491) (root 10) 2 0) DegreeTwoThreeSpectrum2614.graph fusedMap1491swap=true := by decide +kernel
theorem certified1491swap : Certified (graph core1491) (root 10) 2 0 :=
  of_native_maps core1491 DegreeTwoThreeSpectrum2612.graph DegreeTwoThreeSpectrum2614.graph
    sourceMap1491swap fusedMap1491swap sourceMap1491swap_checked fusedMap1491swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1491
#print axioms sourceMap1491swap_checked
#print axioms fusedMap1491swap_checked
#print axioms certified1491swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
