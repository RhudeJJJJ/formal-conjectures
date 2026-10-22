/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5245 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap5245 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5245 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5245_checked : acceptsGraphIso
    (source (graph core5245) (root 7) 2 5) DegreeTwoThreeSpectrum5797.graph sourceMap5245=true := by decide +kernel
theorem fusedMap5245_checked : acceptsGraphIso
    (fused (graph core5245) (root 7) 2 5) DegreeTwoThreeSpectrum5071.graph fusedMap5245=true := by decide +kernel
theorem certified5245 : Certified (graph core5245) (root 7) 2 5 :=
  of_native_maps core5245 DegreeTwoThreeSpectrum5797.graph DegreeTwoThreeSpectrum5071.graph
    sourceMap5245 fusedMap5245 sourceMap5245_checked fusedMap5245_checked
    DegreeTwoThreeFiniteComparisons.comparison5245
#print axioms sourceMap5245_checked
#print axioms fusedMap5245_checked
#print axioms certified5245
def sourceMap5245swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5245swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5245swap_checked : acceptsGraphIso
    (source (graph core5245) (root 7) 5 2) DegreeTwoThreeSpectrum5797.graph sourceMap5245swap=true := by decide +kernel
theorem fusedMap5245swap_checked : acceptsGraphIso
    (fused (graph core5245) (root 7) 5 2) DegreeTwoThreeSpectrum5071.graph fusedMap5245swap=true := by decide +kernel
theorem certified5245swap : Certified (graph core5245) (root 7) 5 2 :=
  of_native_maps core5245 DegreeTwoThreeSpectrum5797.graph DegreeTwoThreeSpectrum5071.graph
    sourceMap5245swap fusedMap5245swap sourceMap5245swap_checked fusedMap5245swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5245
#print axioms sourceMap5245swap_checked
#print axioms fusedMap5245swap_checked
#print axioms certified5245swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
