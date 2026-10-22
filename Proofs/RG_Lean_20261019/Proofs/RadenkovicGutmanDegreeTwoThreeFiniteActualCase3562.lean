/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3562 : Family 8 := level8.get ⟨89,by decide⟩
def sourceMap3562 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3562 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3562_checked : acceptsGraphIso
    (source (graph core3562) (root 8) 0 6) DegreeTwoThreeSpectrum5893.graph sourceMap3562=true := by decide +kernel
theorem fusedMap3562_checked : acceptsGraphIso
    (fused (graph core3562) (root 8) 0 6) DegreeTwoThreeSpectrum5092.graph fusedMap3562=true := by decide +kernel
theorem certified3562 : Certified (graph core3562) (root 8) 0 6 :=
  of_native_maps core3562 DegreeTwoThreeSpectrum5893.graph DegreeTwoThreeSpectrum5092.graph
    sourceMap3562 fusedMap3562 sourceMap3562_checked fusedMap3562_checked
    DegreeTwoThreeFiniteComparisons.comparison3562
#print axioms sourceMap3562_checked
#print axioms fusedMap3562_checked
#print axioms certified3562
def sourceMap3562swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3562swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3562swap_checked : acceptsGraphIso
    (source (graph core3562) (root 8) 6 0) DegreeTwoThreeSpectrum5893.graph sourceMap3562swap=true := by decide +kernel
theorem fusedMap3562swap_checked : acceptsGraphIso
    (fused (graph core3562) (root 8) 6 0) DegreeTwoThreeSpectrum5092.graph fusedMap3562swap=true := by decide +kernel
theorem certified3562swap : Certified (graph core3562) (root 8) 6 0 :=
  of_native_maps core3562 DegreeTwoThreeSpectrum5893.graph DegreeTwoThreeSpectrum5092.graph
    sourceMap3562swap fusedMap3562swap sourceMap3562swap_checked fusedMap3562swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3562
#print axioms sourceMap3562swap_checked
#print axioms fusedMap3562swap_checked
#print axioms certified3562swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
