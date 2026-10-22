/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3881 : Family 8 := level8.get ⟨172,by decide⟩
def sourceMap3881 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3881 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3881_checked : acceptsGraphIso
    (source (graph core3881) (root 8) 1 4) DegreeTwoThreeSpectrum4595.graph sourceMap3881=true := by decide +kernel
theorem fusedMap3881_checked : acceptsGraphIso
    (fused (graph core3881) (root 8) 1 4) DegreeTwoThreeSpectrum4081.graph fusedMap3881=true := by decide +kernel
theorem certified3881 : Certified (graph core3881) (root 8) 1 4 :=
  of_native_maps core3881 DegreeTwoThreeSpectrum4595.graph DegreeTwoThreeSpectrum4081.graph
    sourceMap3881 fusedMap3881 sourceMap3881_checked fusedMap3881_checked
    DegreeTwoThreeFiniteComparisons.comparison3881
#print axioms sourceMap3881_checked
#print axioms fusedMap3881_checked
#print axioms certified3881
def sourceMap3881swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3881swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3881swap_checked : acceptsGraphIso
    (source (graph core3881) (root 8) 4 1) DegreeTwoThreeSpectrum4595.graph sourceMap3881swap=true := by decide +kernel
theorem fusedMap3881swap_checked : acceptsGraphIso
    (fused (graph core3881) (root 8) 4 1) DegreeTwoThreeSpectrum4081.graph fusedMap3881swap=true := by decide +kernel
theorem certified3881swap : Certified (graph core3881) (root 8) 4 1 :=
  of_native_maps core3881 DegreeTwoThreeSpectrum4595.graph DegreeTwoThreeSpectrum4081.graph
    sourceMap3881swap fusedMap3881swap sourceMap3881swap_checked fusedMap3881swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3881
#print axioms sourceMap3881swap_checked
#print axioms fusedMap3881swap_checked
#print axioms certified3881swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
