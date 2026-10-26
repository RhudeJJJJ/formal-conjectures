/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3630 : Family 8 := level8.get ⟨257,by decide⟩
def sourceMap3630 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3630 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3630_checked : acceptsGraphIso
    (source (graph core3630) (root 8) 0 6) DegreeTwoThreeSpectrum6869.graph sourceMap3630=true := by decide +kernel
theorem fusedMap3630_checked : acceptsGraphIso
    (fused (graph core3630) (root 8) 0 6) DegreeTwoThreeSpectrum5671.graph fusedMap3630=true := by decide +kernel
theorem certified3630 : Certified (graph core3630) (root 8) 0 6 :=
  of_native_maps core3630 DegreeTwoThreeSpectrum6869.graph DegreeTwoThreeSpectrum5671.graph
    sourceMap3630 fusedMap3630 sourceMap3630_checked fusedMap3630_checked
    DegreeTwoThreeFiniteComparisons.comparison3630
#print axioms sourceMap3630_checked
#print axioms fusedMap3630_checked
#print axioms certified3630
def sourceMap3630swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3630swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3630swap_checked : acceptsGraphIso
    (source (graph core3630) (root 8) 6 0) DegreeTwoThreeSpectrum6869.graph sourceMap3630swap=true := by decide +kernel
theorem fusedMap3630swap_checked : acceptsGraphIso
    (fused (graph core3630) (root 8) 6 0) DegreeTwoThreeSpectrum5671.graph fusedMap3630swap=true := by decide +kernel
theorem certified3630swap : Certified (graph core3630) (root 8) 6 0 :=
  of_native_maps core3630 DegreeTwoThreeSpectrum6869.graph DegreeTwoThreeSpectrum5671.graph
    sourceMap3630swap fusedMap3630swap sourceMap3630swap_checked fusedMap3630swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3630
#print axioms sourceMap3630swap_checked
#print axioms fusedMap3630swap_checked
#print axioms certified3630swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
