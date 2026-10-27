/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3961 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap3961 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3961 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3961_checked : acceptsGraphIso
    (source (graph core3961) (root 7) 1 5) DegreeTwoThreeSpectrum4477.graph sourceMap3961=true := by decide +kernel
theorem fusedMap3961_checked : acceptsGraphIso
    (fused (graph core3961) (root 7) 1 5) DegreeTwoThreeSpectrum4012.graph fusedMap3961=true := by decide +kernel
theorem certified3961 : Certified (graph core3961) (root 7) 1 5 :=
  of_native_maps core3961 DegreeTwoThreeSpectrum4477.graph DegreeTwoThreeSpectrum4012.graph
    sourceMap3961 fusedMap3961 sourceMap3961_checked fusedMap3961_checked
    DegreeTwoThreeFiniteComparisons.comparison3961
#print axioms sourceMap3961_checked
#print axioms fusedMap3961_checked
#print axioms certified3961
def sourceMap3961swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3961swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3961swap_checked : acceptsGraphIso
    (source (graph core3961) (root 7) 5 1) DegreeTwoThreeSpectrum4477.graph sourceMap3961swap=true := by decide +kernel
theorem fusedMap3961swap_checked : acceptsGraphIso
    (fused (graph core3961) (root 7) 5 1) DegreeTwoThreeSpectrum4012.graph fusedMap3961swap=true := by decide +kernel
theorem certified3961swap : Certified (graph core3961) (root 7) 5 1 :=
  of_native_maps core3961 DegreeTwoThreeSpectrum4477.graph DegreeTwoThreeSpectrum4012.graph
    sourceMap3961swap fusedMap3961swap sourceMap3961swap_checked fusedMap3961swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3961
#print axioms sourceMap3961swap_checked
#print axioms fusedMap3961swap_checked
#print axioms certified3961swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
