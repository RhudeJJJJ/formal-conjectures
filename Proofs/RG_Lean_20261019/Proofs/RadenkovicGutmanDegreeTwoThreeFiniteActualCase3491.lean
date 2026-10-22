/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3491 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap3491 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3491 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3491_checked : acceptsGraphIso
    (source (graph core3491) (root 6) 0 6) DegreeTwoThreeSpectrum2479.graph sourceMap3491=true := by decide +kernel
theorem fusedMap3491_checked : acceptsGraphIso
    (fused (graph core3491) (root 6) 0 6) DegreeTwoThreeSpectrum2316.graph fusedMap3491=true := by decide +kernel
theorem certified3491 : Certified (graph core3491) (root 6) 0 6 :=
  of_native_maps core3491 DegreeTwoThreeSpectrum2479.graph DegreeTwoThreeSpectrum2316.graph
    sourceMap3491 fusedMap3491 sourceMap3491_checked fusedMap3491_checked
    DegreeTwoThreeFiniteComparisons.comparison3491
#print axioms sourceMap3491_checked
#print axioms fusedMap3491_checked
#print axioms certified3491
def sourceMap3491swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3491swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3491swap_checked : acceptsGraphIso
    (source (graph core3491) (root 6) 6 0) DegreeTwoThreeSpectrum2479.graph sourceMap3491swap=true := by decide +kernel
theorem fusedMap3491swap_checked : acceptsGraphIso
    (fused (graph core3491) (root 6) 6 0) DegreeTwoThreeSpectrum2316.graph fusedMap3491swap=true := by decide +kernel
theorem certified3491swap : Certified (graph core3491) (root 6) 6 0 :=
  of_native_maps core3491 DegreeTwoThreeSpectrum2479.graph DegreeTwoThreeSpectrum2316.graph
    sourceMap3491swap fusedMap3491swap sourceMap3491swap_checked fusedMap3491swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3491
#print axioms sourceMap3491swap_checked
#print axioms fusedMap3491swap_checked
#print axioms certified3491swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
