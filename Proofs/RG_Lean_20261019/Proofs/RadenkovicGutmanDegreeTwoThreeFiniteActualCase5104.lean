/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5104 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap5104 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5104 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5104_checked : acceptsGraphIso
    (source (graph core5104) (root 7) 2 4) DegreeTwoThreeSpectrum4729.graph sourceMap5104=true := by decide +kernel
theorem fusedMap5104_checked : acceptsGraphIso
    (fused (graph core5104) (root 7) 2 4) DegreeTwoThreeSpectrum3919.graph fusedMap5104=true := by decide +kernel
theorem certified5104 : Certified (graph core5104) (root 7) 2 4 :=
  of_native_maps core5104 DegreeTwoThreeSpectrum4729.graph DegreeTwoThreeSpectrum3919.graph
    sourceMap5104 fusedMap5104 sourceMap5104_checked fusedMap5104_checked
    DegreeTwoThreeFiniteComparisons.comparison5104
#print axioms sourceMap5104_checked
#print axioms fusedMap5104_checked
#print axioms certified5104
def sourceMap5104swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,8,9,10] (sourceLabel 7 4 2 v)
def fusedMap5104swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5104swap_checked : acceptsGraphIso
    (source (graph core5104) (root 7) 4 2) DegreeTwoThreeSpectrum4729.graph sourceMap5104swap=true := by decide +kernel
theorem fusedMap5104swap_checked : acceptsGraphIso
    (fused (graph core5104) (root 7) 4 2) DegreeTwoThreeSpectrum3919.graph fusedMap5104swap=true := by decide +kernel
theorem certified5104swap : Certified (graph core5104) (root 7) 4 2 :=
  of_native_maps core5104 DegreeTwoThreeSpectrum4729.graph DegreeTwoThreeSpectrum3919.graph
    sourceMap5104swap fusedMap5104swap sourceMap5104swap_checked fusedMap5104swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5104
#print axioms sourceMap5104swap_checked
#print axioms fusedMap5104swap_checked
#print axioms certified5104swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
