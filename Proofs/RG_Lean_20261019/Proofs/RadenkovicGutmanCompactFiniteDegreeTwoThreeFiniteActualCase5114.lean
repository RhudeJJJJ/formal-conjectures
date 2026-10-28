/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5114 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap5114 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,11,6,7,8,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5114 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5114_checked : acceptsGraphIso
    (source (graph core5114) (root 7) 2 4) DegreeTwoThreeSpectrum4840.graph sourceMap5114=true := by decide +kernel
theorem fusedMap5114_checked : acceptsGraphIso
    (fused (graph core5114) (root 7) 2 4) DegreeTwoThreeSpectrum4019.graph fusedMap5114=true := by decide +kernel
theorem certified5114 : Certified (graph core5114) (root 7) 2 4 :=
  of_native_maps core5114 DegreeTwoThreeSpectrum4840.graph DegreeTwoThreeSpectrum4019.graph
    sourceMap5114 fusedMap5114 sourceMap5114_checked fusedMap5114_checked
    DegreeTwoThreeFiniteComparisons.comparison5114
#print axioms sourceMap5114_checked
#print axioms fusedMap5114_checked
#print axioms certified5114
def sourceMap5114swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,11,0,12,13,14,15,6,7,8] (sourceLabel 7 4 2 v)
def fusedMap5114swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5114swap_checked : acceptsGraphIso
    (source (graph core5114) (root 7) 4 2) DegreeTwoThreeSpectrum4840.graph sourceMap5114swap=true := by decide +kernel
theorem fusedMap5114swap_checked : acceptsGraphIso
    (fused (graph core5114) (root 7) 4 2) DegreeTwoThreeSpectrum4019.graph fusedMap5114swap=true := by decide +kernel
theorem certified5114swap : Certified (graph core5114) (root 7) 4 2 :=
  of_native_maps core5114 DegreeTwoThreeSpectrum4840.graph DegreeTwoThreeSpectrum4019.graph
    sourceMap5114swap fusedMap5114swap sourceMap5114swap_checked fusedMap5114swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5114
#print axioms sourceMap5114swap_checked
#print axioms fusedMap5114swap_checked
#print axioms certified5114swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
