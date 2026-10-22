/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2951 : Family 10 := level10.get ⟨1439,by decide⟩
def sourceMap2951 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2951 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2951_checked : acceptsGraphIso
    (source (graph core2951) (root 10) 0 4) DegreeTwoThreeSpectrum6898.graph sourceMap2951=true := by decide +kernel
theorem fusedMap2951_checked : acceptsGraphIso
    (fused (graph core2951) (root 10) 0 4) DegreeTwoThreeSpectrum6899.graph fusedMap2951=true := by decide +kernel
theorem certified2951 : Certified (graph core2951) (root 10) 0 4 :=
  of_native_maps core2951 DegreeTwoThreeSpectrum6898.graph DegreeTwoThreeSpectrum6899.graph
    sourceMap2951 fusedMap2951 sourceMap2951_checked fusedMap2951_checked
    DegreeTwoThreeFiniteComparisons.comparison2951
#print axioms sourceMap2951_checked
#print axioms fusedMap2951_checked
#print axioms certified2951
def sourceMap2951swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2951swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2951swap_checked : acceptsGraphIso
    (source (graph core2951) (root 10) 4 0) DegreeTwoThreeSpectrum6898.graph sourceMap2951swap=true := by decide +kernel
theorem fusedMap2951swap_checked : acceptsGraphIso
    (fused (graph core2951) (root 10) 4 0) DegreeTwoThreeSpectrum6899.graph fusedMap2951swap=true := by decide +kernel
theorem certified2951swap : Certified (graph core2951) (root 10) 4 0 :=
  of_native_maps core2951 DegreeTwoThreeSpectrum6898.graph DegreeTwoThreeSpectrum6899.graph
    sourceMap2951swap fusedMap2951swap sourceMap2951swap_checked fusedMap2951swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2951
#print axioms sourceMap2951swap_checked
#print axioms fusedMap2951swap_checked
#print axioms certified2951swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
