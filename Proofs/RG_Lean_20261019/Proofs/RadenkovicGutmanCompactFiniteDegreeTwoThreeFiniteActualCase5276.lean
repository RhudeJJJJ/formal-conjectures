/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5276 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap5276 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,2,3,4,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5276 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5276_checked : acceptsGraphIso
    (source (graph core5276) (root 7) 2 5) DegreeTwoThreeSpectrum6866.graph sourceMap5276=true := by decide +kernel
theorem fusedMap5276_checked : acceptsGraphIso
    (fused (graph core5276) (root 7) 2 5) DegreeTwoThreeSpectrum5135.graph fusedMap5276=true := by decide +kernel
theorem certified5276 : Certified (graph core5276) (root 7) 2 5 :=
  of_native_maps core5276 DegreeTwoThreeSpectrum6866.graph DegreeTwoThreeSpectrum5135.graph
    sourceMap5276 fusedMap5276 sourceMap5276_checked fusedMap5276_checked
    DegreeTwoThreeFiniteComparisons.comparison5276
#print axioms sourceMap5276_checked
#print axioms fusedMap5276_checked
#print axioms certified5276
def sourceMap5276swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,0,12,13,14,15,16,2,3,4] (sourceLabel 7 5 2 v)
def fusedMap5276swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5276swap_checked : acceptsGraphIso
    (source (graph core5276) (root 7) 5 2) DegreeTwoThreeSpectrum6866.graph sourceMap5276swap=true := by decide +kernel
theorem fusedMap5276swap_checked : acceptsGraphIso
    (fused (graph core5276) (root 7) 5 2) DegreeTwoThreeSpectrum5135.graph fusedMap5276swap=true := by decide +kernel
theorem certified5276swap : Certified (graph core5276) (root 7) 5 2 :=
  of_native_maps core5276 DegreeTwoThreeSpectrum6866.graph DegreeTwoThreeSpectrum5135.graph
    sourceMap5276swap fusedMap5276swap sourceMap5276swap_checked fusedMap5276swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5276
#print axioms sourceMap5276swap_checked
#print axioms fusedMap5276swap_checked
#print axioms certified5276swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
