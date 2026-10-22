/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1922 : Family 10 := level10.get ⟨1427,by decide⟩
def sourceMap1922 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1922 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1922_checked : acceptsGraphIso
    (source (graph core1922) (root 10) 0 2) DegreeTwoThreeSpectrum3650.graph sourceMap1922=true := by decide +kernel
theorem fusedMap1922_checked : acceptsGraphIso
    (fused (graph core1922) (root 10) 0 2) DegreeTwoThreeSpectrum3651.graph fusedMap1922=true := by decide +kernel
theorem certified1922 : Certified (graph core1922) (root 10) 0 2 :=
  of_native_maps core1922 DegreeTwoThreeSpectrum3650.graph DegreeTwoThreeSpectrum3651.graph
    sourceMap1922 fusedMap1922 sourceMap1922_checked fusedMap1922_checked
    DegreeTwoThreeFiniteComparisons.comparison1922
#print axioms sourceMap1922_checked
#print axioms fusedMap1922_checked
#print axioms certified1922
def sourceMap1922swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1922swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1922swap_checked : acceptsGraphIso
    (source (graph core1922) (root 10) 2 0) DegreeTwoThreeSpectrum3650.graph sourceMap1922swap=true := by decide +kernel
theorem fusedMap1922swap_checked : acceptsGraphIso
    (fused (graph core1922) (root 10) 2 0) DegreeTwoThreeSpectrum3651.graph fusedMap1922swap=true := by decide +kernel
theorem certified1922swap : Certified (graph core1922) (root 10) 2 0 :=
  of_native_maps core1922 DegreeTwoThreeSpectrum3650.graph DegreeTwoThreeSpectrum3651.graph
    sourceMap1922swap fusedMap1922swap sourceMap1922swap_checked fusedMap1922swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1922
#print axioms sourceMap1922swap_checked
#print axioms fusedMap1922swap_checked
#print axioms certified1922swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
