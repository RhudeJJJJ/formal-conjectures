/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5112 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap5112 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5112 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5112_checked : acceptsGraphIso
    (source (graph core5112) (root 7) 2 4) DegreeTwoThreeSpectrum4825.graph sourceMap5112=true := by decide +kernel
theorem fusedMap5112_checked : acceptsGraphIso
    (fused (graph core5112) (root 7) 2 4) DegreeTwoThreeSpectrum4004.graph fusedMap5112=true := by decide +kernel
theorem certified5112 : Certified (graph core5112) (root 7) 2 4 :=
  of_native_maps core5112 DegreeTwoThreeSpectrum4825.graph DegreeTwoThreeSpectrum4004.graph
    sourceMap5112 fusedMap5112 sourceMap5112_checked fusedMap5112_checked
    DegreeTwoThreeFiniteComparisons.comparison5112
#print axioms sourceMap5112_checked
#print axioms fusedMap5112_checked
#print axioms certified5112
def sourceMap5112swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5112swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5112swap_checked : acceptsGraphIso
    (source (graph core5112) (root 7) 4 2) DegreeTwoThreeSpectrum4825.graph sourceMap5112swap=true := by decide +kernel
theorem fusedMap5112swap_checked : acceptsGraphIso
    (fused (graph core5112) (root 7) 4 2) DegreeTwoThreeSpectrum4004.graph fusedMap5112swap=true := by decide +kernel
theorem certified5112swap : Certified (graph core5112) (root 7) 4 2 :=
  of_native_maps core5112 DegreeTwoThreeSpectrum4825.graph DegreeTwoThreeSpectrum4004.graph
    sourceMap5112swap fusedMap5112swap sourceMap5112swap_checked fusedMap5112swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5112
#print axioms sourceMap5112swap_checked
#print axioms fusedMap5112swap_checked
#print axioms certified5112swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
