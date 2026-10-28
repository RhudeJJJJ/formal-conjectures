/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5408 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap5408 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5,11,12,13,14,15,16] (sourceLabel 5 4 5 v)
def fusedMap5408 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 4 5 v)
theorem sourceMap5408_checked : acceptsGraphIso
    (source (graph core5408) (root 5) 4 5) DegreeTwoThreeSpectrum5931.graph sourceMap5408=true := by decide +kernel
theorem fusedMap5408_checked : acceptsGraphIso
    (fused (graph core5408) (root 5) 4 5) DegreeTwoThreeSpectrum4973.graph fusedMap5408=true := by decide +kernel
theorem certified5408 : Certified (graph core5408) (root 5) 4 5 :=
  of_native_maps core5408 DegreeTwoThreeSpectrum5931.graph DegreeTwoThreeSpectrum4973.graph
    sourceMap5408 fusedMap5408 sourceMap5408_checked fusedMap5408_checked
    DegreeTwoThreeFiniteComparisons.comparison5408
#print axioms sourceMap5408_checked
#print axioms fusedMap5408_checked
#print axioms certified5408
def sourceMap5408swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,6,7,8,9,10,11,12,13,14,15,16,1,2,3,4,5] (sourceLabel 5 5 4 v)
def fusedMap5408swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 5 4 v)
theorem sourceMap5408swap_checked : acceptsGraphIso
    (source (graph core5408) (root 5) 5 4) DegreeTwoThreeSpectrum5931.graph sourceMap5408swap=true := by decide +kernel
theorem fusedMap5408swap_checked : acceptsGraphIso
    (fused (graph core5408) (root 5) 5 4) DegreeTwoThreeSpectrum4973.graph fusedMap5408swap=true := by decide +kernel
theorem certified5408swap : Certified (graph core5408) (root 5) 5 4 :=
  of_native_maps core5408 DegreeTwoThreeSpectrum5931.graph DegreeTwoThreeSpectrum4973.graph
    sourceMap5408swap fusedMap5408swap sourceMap5408swap_checked fusedMap5408swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5408
#print axioms sourceMap5408swap_checked
#print axioms fusedMap5408swap_checked
#print axioms certified5408swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
