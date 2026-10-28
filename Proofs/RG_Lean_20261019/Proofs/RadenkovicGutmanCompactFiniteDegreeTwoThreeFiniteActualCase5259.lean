/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5259 : Family 7 := level7.get ⟨58,by decide⟩
def sourceMap5259 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5259 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5259_checked : acceptsGraphIso
    (source (graph core5259) (root 7) 2 5) DegreeTwoThreeSpectrum7016.graph sourceMap5259=true := by decide +kernel
theorem fusedMap5259_checked : acceptsGraphIso
    (fused (graph core5259) (root 7) 2 5) DegreeTwoThreeSpectrum5081.graph fusedMap5259=true := by decide +kernel
theorem certified5259 : Certified (graph core5259) (root 7) 2 5 :=
  of_native_maps core5259 DegreeTwoThreeSpectrum7016.graph DegreeTwoThreeSpectrum5081.graph
    sourceMap5259 fusedMap5259 sourceMap5259_checked fusedMap5259_checked
    DegreeTwoThreeFiniteComparisons.comparison5259
#print axioms sourceMap5259_checked
#print axioms fusedMap5259_checked
#print axioms certified5259
def sourceMap5259swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,12,13,14,15,16,9,10,11] (sourceLabel 7 5 2 v)
def fusedMap5259swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5259swap_checked : acceptsGraphIso
    (source (graph core5259) (root 7) 5 2) DegreeTwoThreeSpectrum7016.graph sourceMap5259swap=true := by decide +kernel
theorem fusedMap5259swap_checked : acceptsGraphIso
    (fused (graph core5259) (root 7) 5 2) DegreeTwoThreeSpectrum5081.graph fusedMap5259swap=true := by decide +kernel
theorem certified5259swap : Certified (graph core5259) (root 7) 5 2 :=
  of_native_maps core5259 DegreeTwoThreeSpectrum7016.graph DegreeTwoThreeSpectrum5081.graph
    sourceMap5259swap fusedMap5259swap sourceMap5259swap_checked fusedMap5259swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5259
#print axioms sourceMap5259swap_checked
#print axioms fusedMap5259swap_checked
#print axioms certified5259swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
