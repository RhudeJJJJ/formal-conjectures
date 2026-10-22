/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1878 : Family 10 := level10.get ⟨1325,by decide⟩
def sourceMap1878 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1878 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1878_checked : acceptsGraphIso
    (source (graph core1878) (root 10) 0 2) DegreeTwoThreeSpectrum3499.graph sourceMap1878=true := by decide +kernel
theorem fusedMap1878_checked : acceptsGraphIso
    (fused (graph core1878) (root 10) 0 2) DegreeTwoThreeSpectrum3500.graph fusedMap1878=true := by decide +kernel
theorem certified1878 : Certified (graph core1878) (root 10) 0 2 :=
  of_native_maps core1878 DegreeTwoThreeSpectrum3499.graph DegreeTwoThreeSpectrum3500.graph
    sourceMap1878 fusedMap1878 sourceMap1878_checked fusedMap1878_checked
    DegreeTwoThreeFiniteComparisons.comparison1878
#print axioms sourceMap1878_checked
#print axioms fusedMap1878_checked
#print axioms certified1878
def sourceMap1878swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1878swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1878swap_checked : acceptsGraphIso
    (source (graph core1878) (root 10) 2 0) DegreeTwoThreeSpectrum3499.graph sourceMap1878swap=true := by decide +kernel
theorem fusedMap1878swap_checked : acceptsGraphIso
    (fused (graph core1878) (root 10) 2 0) DegreeTwoThreeSpectrum3500.graph fusedMap1878swap=true := by decide +kernel
theorem certified1878swap : Certified (graph core1878) (root 10) 2 0 :=
  of_native_maps core1878 DegreeTwoThreeSpectrum3499.graph DegreeTwoThreeSpectrum3500.graph
    sourceMap1878swap fusedMap1878swap sourceMap1878swap_checked fusedMap1878swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1878
#print axioms sourceMap1878swap_checked
#print axioms fusedMap1878swap_checked
#print axioms certified1878swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
