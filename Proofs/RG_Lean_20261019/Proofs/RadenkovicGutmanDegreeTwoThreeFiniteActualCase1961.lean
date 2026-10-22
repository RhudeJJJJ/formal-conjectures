/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1961 : Family 10 := level10.get ⟨1533,by decide⟩
def sourceMap1961 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1961 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1961_checked : acceptsGraphIso
    (source (graph core1961) (root 10) 0 2) DegreeTwoThreeSpectrum3742.graph sourceMap1961=true := by decide +kernel
theorem fusedMap1961_checked : acceptsGraphIso
    (fused (graph core1961) (root 10) 0 2) DegreeTwoThreeSpectrum3005.graph fusedMap1961=true := by decide +kernel
theorem certified1961 : Certified (graph core1961) (root 10) 0 2 :=
  of_native_maps core1961 DegreeTwoThreeSpectrum3742.graph DegreeTwoThreeSpectrum3005.graph
    sourceMap1961 fusedMap1961 sourceMap1961_checked fusedMap1961_checked
    DegreeTwoThreeFiniteComparisons.comparison1961
#print axioms sourceMap1961_checked
#print axioms fusedMap1961_checked
#print axioms certified1961
def sourceMap1961swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1961swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1961swap_checked : acceptsGraphIso
    (source (graph core1961) (root 10) 2 0) DegreeTwoThreeSpectrum3742.graph sourceMap1961swap=true := by decide +kernel
theorem fusedMap1961swap_checked : acceptsGraphIso
    (fused (graph core1961) (root 10) 2 0) DegreeTwoThreeSpectrum3005.graph fusedMap1961swap=true := by decide +kernel
theorem certified1961swap : Certified (graph core1961) (root 10) 2 0 :=
  of_native_maps core1961 DegreeTwoThreeSpectrum3742.graph DegreeTwoThreeSpectrum3005.graph
    sourceMap1961swap fusedMap1961swap sourceMap1961swap_checked fusedMap1961swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1961
#print axioms sourceMap1961swap_checked
#print axioms fusedMap1961swap_checked
#print axioms certified1961swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
