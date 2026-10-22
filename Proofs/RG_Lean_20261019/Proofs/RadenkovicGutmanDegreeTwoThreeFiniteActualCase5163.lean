/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5163 : Family 8 := level8.get ⟨147,by decide⟩
def sourceMap5163 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5163 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5163_checked : acceptsGraphIso
    (source (graph core5163) (root 8) 2 4) DegreeTwoThreeSpectrum6659.graph sourceMap5163=true := by decide +kernel
theorem fusedMap5163_checked : acceptsGraphIso
    (fused (graph core5163) (root 8) 2 4) DegreeTwoThreeSpectrum5521.graph fusedMap5163=true := by decide +kernel
theorem certified5163 : Certified (graph core5163) (root 8) 2 4 :=
  of_native_maps core5163 DegreeTwoThreeSpectrum6659.graph DegreeTwoThreeSpectrum5521.graph
    sourceMap5163 fusedMap5163 sourceMap5163_checked fusedMap5163_checked
    DegreeTwoThreeFiniteComparisons.comparison5163
#print axioms sourceMap5163_checked
#print axioms fusedMap5163_checked
#print axioms certified5163
def sourceMap5163swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5163swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5163swap_checked : acceptsGraphIso
    (source (graph core5163) (root 8) 4 2) DegreeTwoThreeSpectrum6659.graph sourceMap5163swap=true := by decide +kernel
theorem fusedMap5163swap_checked : acceptsGraphIso
    (fused (graph core5163) (root 8) 4 2) DegreeTwoThreeSpectrum5521.graph fusedMap5163swap=true := by decide +kernel
theorem certified5163swap : Certified (graph core5163) (root 8) 4 2 :=
  of_native_maps core5163 DegreeTwoThreeSpectrum6659.graph DegreeTwoThreeSpectrum5521.graph
    sourceMap5163swap fusedMap5163swap sourceMap5163swap_checked fusedMap5163swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5163
#print axioms sourceMap5163swap_checked
#print axioms fusedMap5163swap_checked
#print axioms certified5163swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
