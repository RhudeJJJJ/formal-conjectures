/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1433 : Family 10 := level10.get ⟨25,by decide⟩
def sourceMap1433 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1433 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1433_checked : acceptsGraphIso
    (source (graph core1433) (root 10) 0 2) DegreeTwoThreeSpectrum2375.graph sourceMap1433=true := by decide +kernel
theorem fusedMap1433_checked : acceptsGraphIso
    (fused (graph core1433) (root 10) 0 2) DegreeTwoThreeSpectrum2378.graph fusedMap1433=true := by decide +kernel
theorem certified1433 : Certified (graph core1433) (root 10) 0 2 :=
  of_native_maps core1433 DegreeTwoThreeSpectrum2375.graph DegreeTwoThreeSpectrum2378.graph
    sourceMap1433 fusedMap1433 sourceMap1433_checked fusedMap1433_checked
    DegreeTwoThreeFiniteComparisons.comparison1433
#print axioms sourceMap1433_checked
#print axioms fusedMap1433_checked
#print axioms certified1433
def sourceMap1433swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1433swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1433swap_checked : acceptsGraphIso
    (source (graph core1433) (root 10) 2 0) DegreeTwoThreeSpectrum2375.graph sourceMap1433swap=true := by decide +kernel
theorem fusedMap1433swap_checked : acceptsGraphIso
    (fused (graph core1433) (root 10) 2 0) DegreeTwoThreeSpectrum2378.graph fusedMap1433swap=true := by decide +kernel
theorem certified1433swap : Certified (graph core1433) (root 10) 2 0 :=
  of_native_maps core1433 DegreeTwoThreeSpectrum2375.graph DegreeTwoThreeSpectrum2378.graph
    sourceMap1433swap fusedMap1433swap sourceMap1433swap_checked fusedMap1433swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1433
#print axioms sourceMap1433swap_checked
#print axioms fusedMap1433swap_checked
#print axioms certified1433swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
