/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3311 : Family 9 := level9.get ⟨269,by decide⟩
def sourceMap3311 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3311 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3311_checked : acceptsGraphIso
    (source (graph core3311) (root 9) 0 5) DegreeTwoThreeSpectrum5733.graph sourceMap3311=true := by decide +kernel
theorem fusedMap3311_checked : acceptsGraphIso
    (fused (graph core3311) (root 9) 0 5) DegreeTwoThreeSpectrum5734.graph fusedMap3311=true := by decide +kernel
theorem certified3311 : Certified (graph core3311) (root 9) 0 5 :=
  of_native_maps core3311 DegreeTwoThreeSpectrum5733.graph DegreeTwoThreeSpectrum5734.graph
    sourceMap3311 fusedMap3311 sourceMap3311_checked fusedMap3311_checked
    DegreeTwoThreeFiniteComparisons.comparison3311
#print axioms sourceMap3311_checked
#print axioms fusedMap3311_checked
#print axioms certified3311
def sourceMap3311swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3311swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3311swap_checked : acceptsGraphIso
    (source (graph core3311) (root 9) 5 0) DegreeTwoThreeSpectrum5733.graph sourceMap3311swap=true := by decide +kernel
theorem fusedMap3311swap_checked : acceptsGraphIso
    (fused (graph core3311) (root 9) 5 0) DegreeTwoThreeSpectrum5734.graph fusedMap3311swap=true := by decide +kernel
theorem certified3311swap : Certified (graph core3311) (root 9) 5 0 :=
  of_native_maps core3311 DegreeTwoThreeSpectrum5733.graph DegreeTwoThreeSpectrum5734.graph
    sourceMap3311swap fusedMap3311swap sourceMap3311swap_checked fusedMap3311swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3311
#print axioms sourceMap3311swap_checked
#print axioms fusedMap3311swap_checked
#print axioms certified3311swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
