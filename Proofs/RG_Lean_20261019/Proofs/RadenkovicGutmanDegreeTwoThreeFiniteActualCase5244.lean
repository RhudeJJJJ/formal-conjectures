/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5244 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap5244 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5244 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5244_checked : acceptsGraphIso
    (source (graph core5244) (root 7) 2 5) DegreeTwoThreeSpectrum5633.graph sourceMap5244=true := by decide +kernel
theorem fusedMap5244_checked : acceptsGraphIso
    (fused (graph core5244) (root 7) 2 5) DegreeTwoThreeSpectrum5038.graph fusedMap5244=true := by decide +kernel
theorem certified5244 : Certified (graph core5244) (root 7) 2 5 :=
  of_native_maps core5244 DegreeTwoThreeSpectrum5633.graph DegreeTwoThreeSpectrum5038.graph
    sourceMap5244 fusedMap5244 sourceMap5244_checked fusedMap5244_checked
    DegreeTwoThreeFiniteComparisons.comparison5244
#print axioms sourceMap5244_checked
#print axioms fusedMap5244_checked
#print axioms certified5244
def sourceMap5244swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5244swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5244swap_checked : acceptsGraphIso
    (source (graph core5244) (root 7) 5 2) DegreeTwoThreeSpectrum5633.graph sourceMap5244swap=true := by decide +kernel
theorem fusedMap5244swap_checked : acceptsGraphIso
    (fused (graph core5244) (root 7) 5 2) DegreeTwoThreeSpectrum5038.graph fusedMap5244swap=true := by decide +kernel
theorem certified5244swap : Certified (graph core5244) (root 7) 5 2 :=
  of_native_maps core5244 DegreeTwoThreeSpectrum5633.graph DegreeTwoThreeSpectrum5038.graph
    sourceMap5244swap fusedMap5244swap sourceMap5244swap_checked fusedMap5244swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5244
#print axioms sourceMap5244swap_checked
#print axioms fusedMap5244swap_checked
#print axioms certified5244swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
