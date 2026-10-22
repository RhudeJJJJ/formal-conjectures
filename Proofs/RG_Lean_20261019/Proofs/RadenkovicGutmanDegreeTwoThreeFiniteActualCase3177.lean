/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3177 : Family 8 := level8.get ⟨128,by decide⟩
def sourceMap3177 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3177 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3177_checked : acceptsGraphIso
    (source (graph core3177) (root 8) 0 5) DegreeTwoThreeSpectrum4375.graph sourceMap3177=true := by decide +kernel
theorem fusedMap3177_checked : acceptsGraphIso
    (fused (graph core3177) (root 8) 0 5) DegreeTwoThreeSpectrum3959.graph fusedMap3177=true := by decide +kernel
theorem certified3177 : Certified (graph core3177) (root 8) 0 5 :=
  of_native_maps core3177 DegreeTwoThreeSpectrum4375.graph DegreeTwoThreeSpectrum3959.graph
    sourceMap3177 fusedMap3177 sourceMap3177_checked fusedMap3177_checked
    DegreeTwoThreeFiniteComparisons.comparison3177
#print axioms sourceMap3177_checked
#print axioms fusedMap3177_checked
#print axioms certified3177
def sourceMap3177swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3177swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3177swap_checked : acceptsGraphIso
    (source (graph core3177) (root 8) 5 0) DegreeTwoThreeSpectrum4375.graph sourceMap3177swap=true := by decide +kernel
theorem fusedMap3177swap_checked : acceptsGraphIso
    (fused (graph core3177) (root 8) 5 0) DegreeTwoThreeSpectrum3959.graph fusedMap3177swap=true := by decide +kernel
theorem certified3177swap : Certified (graph core3177) (root 8) 5 0 :=
  of_native_maps core3177 DegreeTwoThreeSpectrum4375.graph DegreeTwoThreeSpectrum3959.graph
    sourceMap3177swap fusedMap3177swap sourceMap3177swap_checked fusedMap3177swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3177
#print axioms sourceMap3177swap_checked
#print axioms fusedMap3177swap_checked
#print axioms certified3177swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
