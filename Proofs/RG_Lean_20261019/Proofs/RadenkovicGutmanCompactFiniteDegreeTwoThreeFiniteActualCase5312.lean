/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5312 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap5312 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,7,8,9,1,0,11,12,13,14,15,16] (sourceLabel 5 2 7 v)
def fusedMap5312 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 2 7 v)
theorem sourceMap5312_checked : acceptsGraphIso
    (source (graph core5312) (root 5) 2 7) DegreeTwoThreeSpectrum5307.graph sourceMap5312=true := by decide +kernel
theorem fusedMap5312_checked : acceptsGraphIso
    (fused (graph core5312) (root 5) 2 7) DegreeTwoThreeSpectrum4987.graph fusedMap5312=true := by decide +kernel
theorem certified5312 : Certified (graph core5312) (root 5) 2 7 :=
  of_native_maps core5312 DegreeTwoThreeSpectrum5307.graph DegreeTwoThreeSpectrum4987.graph
    sourceMap5312 fusedMap5312 sourceMap5312_checked fusedMap5312_checked
    DegreeTwoThreeFiniteComparisons.comparison5312
#print axioms sourceMap5312_checked
#print axioms fusedMap5312_checked
#print axioms certified5312
def sourceMap5312swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,1,0,11,12,13,14,15,16,7,8,9] (sourceLabel 5 7 2 v)
def fusedMap5312swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 7 2 v)
theorem sourceMap5312swap_checked : acceptsGraphIso
    (source (graph core5312) (root 5) 7 2) DegreeTwoThreeSpectrum5307.graph sourceMap5312swap=true := by decide +kernel
theorem fusedMap5312swap_checked : acceptsGraphIso
    (fused (graph core5312) (root 5) 7 2) DegreeTwoThreeSpectrum4987.graph fusedMap5312swap=true := by decide +kernel
theorem certified5312swap : Certified (graph core5312) (root 5) 7 2 :=
  of_native_maps core5312 DegreeTwoThreeSpectrum5307.graph DegreeTwoThreeSpectrum4987.graph
    sourceMap5312swap fusedMap5312swap sourceMap5312swap_checked fusedMap5312swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5312
#print axioms sourceMap5312swap_checked
#print axioms fusedMap5312swap_checked
#print axioms certified5312swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
