/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5314 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap5314 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,9,10,6,7,8,1,0,11,12,13,14,15,16] (sourceLabel 5 2 7 v)
def fusedMap5314 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 2 7 v)
theorem sourceMap5314_checked : acceptsGraphIso
    (source (graph core5314) (root 5) 2 7) DegreeTwoThreeSpectrum5655.graph sourceMap5314=true := by decide +kernel
theorem fusedMap5314_checked : acceptsGraphIso
    (fused (graph core5314) (root 5) 2 7) DegreeTwoThreeSpectrum5055.graph fusedMap5314=true := by decide +kernel
theorem certified5314 : Certified (graph core5314) (root 5) 2 7 :=
  of_native_maps core5314 DegreeTwoThreeSpectrum5655.graph DegreeTwoThreeSpectrum5055.graph
    sourceMap5314 fusedMap5314 sourceMap5314_checked fusedMap5314_checked
    DegreeTwoThreeFiniteComparisons.comparison5314
#print axioms sourceMap5314_checked
#print axioms fusedMap5314_checked
#print axioms certified5314
def sourceMap5314swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,9,10,1,0,11,12,13,14,15,16,6,7,8] (sourceLabel 5 7 2 v)
def fusedMap5314swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 7 2 v)
theorem sourceMap5314swap_checked : acceptsGraphIso
    (source (graph core5314) (root 5) 7 2) DegreeTwoThreeSpectrum5655.graph sourceMap5314swap=true := by decide +kernel
theorem fusedMap5314swap_checked : acceptsGraphIso
    (fused (graph core5314) (root 5) 7 2) DegreeTwoThreeSpectrum5055.graph fusedMap5314swap=true := by decide +kernel
theorem certified5314swap : Certified (graph core5314) (root 5) 7 2 :=
  of_native_maps core5314 DegreeTwoThreeSpectrum5655.graph DegreeTwoThreeSpectrum5055.graph
    sourceMap5314swap fusedMap5314swap sourceMap5314swap_checked fusedMap5314swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5314
#print axioms sourceMap5314swap_checked
#print axioms fusedMap5314swap_checked
#print axioms certified5314swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
