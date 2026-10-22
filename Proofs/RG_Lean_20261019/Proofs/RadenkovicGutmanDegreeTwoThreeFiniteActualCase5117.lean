/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5117 : Family 7 := level7.get ⟨102,by decide⟩
def sourceMap5117 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,11,2,3,4,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5117 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5117_checked : acceptsGraphIso
    (source (graph core5117) (root 7) 2 4) DegreeTwoThreeSpectrum4901.graph sourceMap5117=true := by decide +kernel
theorem fusedMap5117_checked : acceptsGraphIso
    (fused (graph core5117) (root 7) 2 4) DegreeTwoThreeSpectrum4185.graph fusedMap5117=true := by decide +kernel
theorem certified5117 : Certified (graph core5117) (root 7) 2 4 :=
  of_native_maps core5117 DegreeTwoThreeSpectrum4901.graph DegreeTwoThreeSpectrum4185.graph
    sourceMap5117 fusedMap5117 sourceMap5117_checked fusedMap5117_checked
    DegreeTwoThreeFiniteComparisons.comparison5117
#print axioms sourceMap5117_checked
#print axioms fusedMap5117_checked
#print axioms certified5117
def sourceMap5117swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,5,6,7,8,9,10,11,0,12,13,14,15,2,3,4] (sourceLabel 7 4 2 v)
def fusedMap5117swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5117swap_checked : acceptsGraphIso
    (source (graph core5117) (root 7) 4 2) DegreeTwoThreeSpectrum4901.graph sourceMap5117swap=true := by decide +kernel
theorem fusedMap5117swap_checked : acceptsGraphIso
    (fused (graph core5117) (root 7) 4 2) DegreeTwoThreeSpectrum4185.graph fusedMap5117swap=true := by decide +kernel
theorem certified5117swap : Certified (graph core5117) (root 7) 4 2 :=
  of_native_maps core5117 DegreeTwoThreeSpectrum4901.graph DegreeTwoThreeSpectrum4185.graph
    sourceMap5117swap fusedMap5117swap sourceMap5117swap_checked fusedMap5117swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5117
#print axioms sourceMap5117swap_checked
#print axioms fusedMap5117swap_checked
#print axioms certified5117swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
