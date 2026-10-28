/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5353 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5353 : (Vertices 3 ⊕ Fin 4 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,6,7,8,2,3,4,5,0,9,10,11,12,13] (sourceLabel 3 3 5 v)
def fusedMap5353 : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 3 5 v)
theorem sourceMap5353_checked : acceptsGraphIso
    (source (graph core5353) (root 3) 3 5) DegreeTwoThreeSpectrum1914.graph sourceMap5353=true := by decide +kernel
theorem fusedMap5353_checked : acceptsGraphIso
    (fused (graph core5353) (root 3) 3 5) DegreeTwoThreeSpectrum1722.graph fusedMap5353=true := by decide +kernel
theorem certified5353 : Certified (graph core5353) (root 3) 3 5 :=
  of_native_maps core5353 DegreeTwoThreeSpectrum1914.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap5353 fusedMap5353 sourceMap5353_checked fusedMap5353_checked
    DegreeTwoThreeFiniteComparisons.comparison5353
#print axioms sourceMap5353_checked
#print axioms fusedMap5353_checked
#print axioms certified5353
def sourceMap5353swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,6,7,8,0,9,10,11,12,13,2,3,4,5] (sourceLabel 3 5 3 v)
def fusedMap5353swap : (Vertices 3 ⊕ Fin 10) → Fin 14 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13] (fusedLabel 3 5 3 v)
theorem sourceMap5353swap_checked : acceptsGraphIso
    (source (graph core5353) (root 3) 5 3) DegreeTwoThreeSpectrum1914.graph sourceMap5353swap=true := by decide +kernel
theorem fusedMap5353swap_checked : acceptsGraphIso
    (fused (graph core5353) (root 3) 5 3) DegreeTwoThreeSpectrum1722.graph fusedMap5353swap=true := by decide +kernel
theorem certified5353swap : Certified (graph core5353) (root 3) 5 3 :=
  of_native_maps core5353 DegreeTwoThreeSpectrum1914.graph DegreeTwoThreeSpectrum1722.graph
    sourceMap5353swap fusedMap5353swap sourceMap5353swap_checked fusedMap5353swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5353
#print axioms sourceMap5353swap_checked
#print axioms fusedMap5353swap_checked
#print axioms certified5353swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
