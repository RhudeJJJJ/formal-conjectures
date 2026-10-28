/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5343 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap5343 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5343 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5343_checked : acceptsGraphIso
    (source (graph core5343) (root 6) 3 4) DegreeTwoThreeSpectrum4632.graph sourceMap5343=true := by decide +kernel
theorem fusedMap5343_checked : acceptsGraphIso
    (fused (graph core5343) (root 6) 3 4) DegreeTwoThreeSpectrum3946.graph fusedMap5343=true := by decide +kernel
theorem certified5343 : Certified (graph core5343) (root 6) 3 4 :=
  of_native_maps core5343 DegreeTwoThreeSpectrum4632.graph DegreeTwoThreeSpectrum3946.graph
    sourceMap5343 fusedMap5343 sourceMap5343_checked fusedMap5343_checked
    DegreeTwoThreeFiniteComparisons.comparison5343
#print axioms sourceMap5343_checked
#print axioms fusedMap5343_checked
#print axioms certified5343
def sourceMap5343swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5343swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5343swap_checked : acceptsGraphIso
    (source (graph core5343) (root 6) 4 3) DegreeTwoThreeSpectrum4632.graph sourceMap5343swap=true := by decide +kernel
theorem fusedMap5343swap_checked : acceptsGraphIso
    (fused (graph core5343) (root 6) 4 3) DegreeTwoThreeSpectrum3946.graph fusedMap5343swap=true := by decide +kernel
theorem certified5343swap : Certified (graph core5343) (root 6) 4 3 :=
  of_native_maps core5343 DegreeTwoThreeSpectrum4632.graph DegreeTwoThreeSpectrum3946.graph
    sourceMap5343swap fusedMap5343swap sourceMap5343swap_checked fusedMap5343swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5343
#print axioms sourceMap5343swap_checked
#print axioms fusedMap5343swap_checked
#print axioms certified5343swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
