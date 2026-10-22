/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1772 : Family 10 := level10.get ⟨1062,by decide⟩
def sourceMap1772 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1772 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1772_checked : acceptsGraphIso
    (source (graph core1772) (root 10) 0 2) DegreeTwoThreeSpectrum3107.graph sourceMap1772=true := by decide +kernel
theorem fusedMap1772_checked : acceptsGraphIso
    (fused (graph core1772) (root 10) 0 2) DegreeTwoThreeSpectrum3111.graph fusedMap1772=true := by decide +kernel
theorem certified1772 : Certified (graph core1772) (root 10) 0 2 :=
  of_native_maps core1772 DegreeTwoThreeSpectrum3107.graph DegreeTwoThreeSpectrum3111.graph
    sourceMap1772 fusedMap1772 sourceMap1772_checked fusedMap1772_checked
    DegreeTwoThreeFiniteComparisons.comparison1772
#print axioms sourceMap1772_checked
#print axioms fusedMap1772_checked
#print axioms certified1772
def sourceMap1772swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1772swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1772swap_checked : acceptsGraphIso
    (source (graph core1772) (root 10) 2 0) DegreeTwoThreeSpectrum3107.graph sourceMap1772swap=true := by decide +kernel
theorem fusedMap1772swap_checked : acceptsGraphIso
    (fused (graph core1772) (root 10) 2 0) DegreeTwoThreeSpectrum3111.graph fusedMap1772swap=true := by decide +kernel
theorem certified1772swap : Certified (graph core1772) (root 10) 2 0 :=
  of_native_maps core1772 DegreeTwoThreeSpectrum3107.graph DegreeTwoThreeSpectrum3111.graph
    sourceMap1772swap fusedMap1772swap sourceMap1772swap_checked fusedMap1772swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1772
#print axioms sourceMap1772swap_checked
#print axioms fusedMap1772swap_checked
#print axioms certified1772swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
