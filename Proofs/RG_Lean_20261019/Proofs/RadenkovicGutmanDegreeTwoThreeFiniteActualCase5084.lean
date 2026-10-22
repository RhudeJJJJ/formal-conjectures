/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5084 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap5084 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,12,13,14,7,8,9,10,11] (sourceLabel 7 2 4 v)
def fusedMap5084 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5084_checked : acceptsGraphIso
    (source (graph core5084) (root 7) 2 4) DegreeTwoThreeSpectrum4536.graph sourceMap5084=true := by decide +kernel
theorem fusedMap5084_checked : acceptsGraphIso
    (fused (graph core5084) (root 7) 2 4) DegreeTwoThreeSpectrum3866.graph fusedMap5084=true := by decide +kernel
theorem certified5084 : Certified (graph core5084) (root 7) 2 4 :=
  of_native_maps core5084 DegreeTwoThreeSpectrum4536.graph DegreeTwoThreeSpectrum3866.graph
    sourceMap5084 fusedMap5084 sourceMap5084_checked fusedMap5084_checked
    DegreeTwoThreeFiniteComparisons.comparison5084
#print axioms sourceMap5084_checked
#print axioms fusedMap5084_checked
#print axioms certified5084
def sourceMap5084swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,15,7,8,9,10,11,12,13,14] (sourceLabel 7 4 2 v)
def fusedMap5084swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5084swap_checked : acceptsGraphIso
    (source (graph core5084) (root 7) 4 2) DegreeTwoThreeSpectrum4536.graph sourceMap5084swap=true := by decide +kernel
theorem fusedMap5084swap_checked : acceptsGraphIso
    (fused (graph core5084) (root 7) 4 2) DegreeTwoThreeSpectrum3866.graph fusedMap5084swap=true := by decide +kernel
theorem certified5084swap : Certified (graph core5084) (root 7) 4 2 :=
  of_native_maps core5084 DegreeTwoThreeSpectrum4536.graph DegreeTwoThreeSpectrum3866.graph
    sourceMap5084swap fusedMap5084swap sourceMap5084swap_checked fusedMap5084swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5084
#print axioms sourceMap5084swap_checked
#print axioms fusedMap5084swap_checked
#print axioms certified5084swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
