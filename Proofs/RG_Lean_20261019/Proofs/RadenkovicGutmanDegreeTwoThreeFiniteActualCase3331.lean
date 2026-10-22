/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3331 : Family 9 := level9.get ⟨320,by decide⟩
def sourceMap3331 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3331 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3331_checked : acceptsGraphIso
    (source (graph core3331) (root 9) 0 5) DegreeTwoThreeSpectrum5991.graph sourceMap3331=true := by decide +kernel
theorem fusedMap3331_checked : acceptsGraphIso
    (fused (graph core3331) (root 9) 0 5) DegreeTwoThreeSpectrum5137.graph fusedMap3331=true := by decide +kernel
theorem certified3331 : Certified (graph core3331) (root 9) 0 5 :=
  of_native_maps core3331 DegreeTwoThreeSpectrum5991.graph DegreeTwoThreeSpectrum5137.graph
    sourceMap3331 fusedMap3331 sourceMap3331_checked fusedMap3331_checked
    DegreeTwoThreeFiniteComparisons.comparison3331
#print axioms sourceMap3331_checked
#print axioms fusedMap3331_checked
#print axioms certified3331
def sourceMap3331swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3331swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3331swap_checked : acceptsGraphIso
    (source (graph core3331) (root 9) 5 0) DegreeTwoThreeSpectrum5991.graph sourceMap3331swap=true := by decide +kernel
theorem fusedMap3331swap_checked : acceptsGraphIso
    (fused (graph core3331) (root 9) 5 0) DegreeTwoThreeSpectrum5137.graph fusedMap3331swap=true := by decide +kernel
theorem certified3331swap : Certified (graph core3331) (root 9) 5 0 :=
  of_native_maps core3331 DegreeTwoThreeSpectrum5991.graph DegreeTwoThreeSpectrum5137.graph
    sourceMap3331swap fusedMap3331swap sourceMap3331swap_checked fusedMap3331swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3331
#print axioms sourceMap3331swap_checked
#print axioms fusedMap3331swap_checked
#print axioms certified3331swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
