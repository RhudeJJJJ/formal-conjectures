/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3946 : Family 6 := level6.get ⟨34,by decide⟩
def sourceMap3946 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3946 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3946_checked : acceptsGraphIso
    (source (graph core3946) (root 6) 1 5) DegreeTwoThreeSpectrum2830.graph sourceMap3946=true := by decide +kernel
theorem fusedMap3946_checked : acceptsGraphIso
    (fused (graph core3946) (root 6) 1 5) DegreeTwoThreeSpectrum2382.graph fusedMap3946=true := by decide +kernel
theorem certified3946 : Certified (graph core3946) (root 6) 1 5 :=
  of_native_maps core3946 DegreeTwoThreeSpectrum2830.graph DegreeTwoThreeSpectrum2382.graph
    sourceMap3946 fusedMap3946 sourceMap3946_checked fusedMap3946_checked
    DegreeTwoThreeFiniteComparisons.comparison3946
#print axioms sourceMap3946_checked
#print axioms fusedMap3946_checked
#print axioms certified3946
def sourceMap3946swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,14,8,9] (sourceLabel 6 5 1 v)
def fusedMap3946swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3946swap_checked : acceptsGraphIso
    (source (graph core3946) (root 6) 5 1) DegreeTwoThreeSpectrum2830.graph sourceMap3946swap=true := by decide +kernel
theorem fusedMap3946swap_checked : acceptsGraphIso
    (fused (graph core3946) (root 6) 5 1) DegreeTwoThreeSpectrum2382.graph fusedMap3946swap=true := by decide +kernel
theorem certified3946swap : Certified (graph core3946) (root 6) 5 1 :=
  of_native_maps core3946 DegreeTwoThreeSpectrum2830.graph DegreeTwoThreeSpectrum2382.graph
    sourceMap3946swap fusedMap3946swap sourceMap3946swap_checked fusedMap3946swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3946
#print axioms sourceMap3946swap_checked
#print axioms fusedMap3946swap_checked
#print axioms certified3946swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
