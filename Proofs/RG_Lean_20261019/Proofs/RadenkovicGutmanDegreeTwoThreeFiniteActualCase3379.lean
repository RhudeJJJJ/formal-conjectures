/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3379 : Family 9 := level9.get ⟨444,by decide⟩
def sourceMap3379 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3379 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3379_checked : acceptsGraphIso
    (source (graph core3379) (root 9) 0 5) DegreeTwoThreeSpectrum6616.graph sourceMap3379=true := by decide +kernel
theorem fusedMap3379_checked : acceptsGraphIso
    (fused (graph core3379) (root 9) 0 5) DegreeTwoThreeSpectrum5490.graph fusedMap3379=true := by decide +kernel
theorem certified3379 : Certified (graph core3379) (root 9) 0 5 :=
  of_native_maps core3379 DegreeTwoThreeSpectrum6616.graph DegreeTwoThreeSpectrum5490.graph
    sourceMap3379 fusedMap3379 sourceMap3379_checked fusedMap3379_checked
    DegreeTwoThreeFiniteComparisons.comparison3379
#print axioms sourceMap3379_checked
#print axioms fusedMap3379_checked
#print axioms certified3379
def sourceMap3379swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3379swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3379swap_checked : acceptsGraphIso
    (source (graph core3379) (root 9) 5 0) DegreeTwoThreeSpectrum6616.graph sourceMap3379swap=true := by decide +kernel
theorem fusedMap3379swap_checked : acceptsGraphIso
    (fused (graph core3379) (root 9) 5 0) DegreeTwoThreeSpectrum5490.graph fusedMap3379swap=true := by decide +kernel
theorem certified3379swap : Certified (graph core3379) (root 9) 5 0 :=
  of_native_maps core3379 DegreeTwoThreeSpectrum6616.graph DegreeTwoThreeSpectrum5490.graph
    sourceMap3379swap fusedMap3379swap sourceMap3379swap_checked fusedMap3379swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3379
#print axioms sourceMap3379swap_checked
#print axioms fusedMap3379swap_checked
#print axioms certified3379swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
