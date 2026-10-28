/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5299 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap5299 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,11,8,9,10,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5299 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5299_checked : acceptsGraphIso
    (source (graph core5299) (root 6) 2 6) DegreeTwoThreeSpectrum6624.graph sourceMap5299=true := by decide +kernel
theorem fusedMap5299_checked : acceptsGraphIso
    (fused (graph core5299) (root 6) 2 6) DegreeTwoThreeSpectrum5015.graph fusedMap5299=true := by decide +kernel
theorem certified5299 : Certified (graph core5299) (root 6) 2 6 :=
  of_native_maps core5299 DegreeTwoThreeSpectrum6624.graph DegreeTwoThreeSpectrum5015.graph
    sourceMap5299 fusedMap5299 sourceMap5299_checked fusedMap5299_checked
    DegreeTwoThreeFiniteComparisons.comparison5299
#print axioms sourceMap5299_checked
#print axioms fusedMap5299_checked
#print axioms certified5299
def sourceMap5299swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,11,1,0,12,13,14,15,16,8,9,10] (sourceLabel 6 6 2 v)
def fusedMap5299swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5299swap_checked : acceptsGraphIso
    (source (graph core5299) (root 6) 6 2) DegreeTwoThreeSpectrum6624.graph sourceMap5299swap=true := by decide +kernel
theorem fusedMap5299swap_checked : acceptsGraphIso
    (fused (graph core5299) (root 6) 6 2) DegreeTwoThreeSpectrum5015.graph fusedMap5299swap=true := by decide +kernel
theorem certified5299swap : Certified (graph core5299) (root 6) 6 2 :=
  of_native_maps core5299 DegreeTwoThreeSpectrum6624.graph DegreeTwoThreeSpectrum5015.graph
    sourceMap5299swap fusedMap5299swap sourceMap5299swap_checked fusedMap5299swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5299
#print axioms sourceMap5299swap_checked
#print axioms fusedMap5299swap_checked
#print axioms certified5299swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
