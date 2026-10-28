/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5359 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap5359 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,2,3,4,5,0,11,12,13,14,15] (sourceLabel 5 3 5 v)
def fusedMap5359 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 3 5 v)
theorem sourceMap5359_checked : acceptsGraphIso
    (source (graph core5359) (root 5) 3 5) DegreeTwoThreeSpectrum4639.graph sourceMap5359=true := by decide +kernel
theorem fusedMap5359_checked : acceptsGraphIso
    (fused (graph core5359) (root 5) 3 5) DegreeTwoThreeSpectrum3864.graph fusedMap5359=true := by decide +kernel
theorem certified5359 : Certified (graph core5359) (root 5) 3 5 :=
  of_native_maps core5359 DegreeTwoThreeSpectrum4639.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap5359 fusedMap5359 sourceMap5359_checked fusedMap5359_checked
    DegreeTwoThreeFiniteComparisons.comparison5359
#print axioms sourceMap5359_checked
#print axioms fusedMap5359_checked
#print axioms certified5359
def sourceMap5359swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 4) → Fin 16 :=
  fun v => ![1,6,7,8,9,10,0,11,12,13,14,15,2,3,4,5] (sourceLabel 5 5 3 v)
def fusedMap5359swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 5 3 v)
theorem sourceMap5359swap_checked : acceptsGraphIso
    (source (graph core5359) (root 5) 5 3) DegreeTwoThreeSpectrum4639.graph sourceMap5359swap=true := by decide +kernel
theorem fusedMap5359swap_checked : acceptsGraphIso
    (fused (graph core5359) (root 5) 5 3) DegreeTwoThreeSpectrum3864.graph fusedMap5359swap=true := by decide +kernel
theorem certified5359swap : Certified (graph core5359) (root 5) 5 3 :=
  of_native_maps core5359 DegreeTwoThreeSpectrum4639.graph DegreeTwoThreeSpectrum3864.graph
    sourceMap5359swap fusedMap5359swap sourceMap5359swap_checked fusedMap5359swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5359
#print axioms sourceMap5359swap_checked
#print axioms fusedMap5359swap_checked
#print axioms certified5359swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
