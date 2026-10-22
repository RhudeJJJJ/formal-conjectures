/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5273 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap5273 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5273 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5273_checked : acceptsGraphIso
    (source (graph core5273) (root 7) 2 5) DegreeTwoThreeSpectrum6676.graph sourceMap5273=true := by decide +kernel
theorem fusedMap5273_checked : acceptsGraphIso
    (fused (graph core5273) (root 7) 2 5) DegreeTwoThreeSpectrum5544.graph fusedMap5273=true := by decide +kernel
theorem certified5273 : Certified (graph core5273) (root 7) 2 5 :=
  of_native_maps core5273 DegreeTwoThreeSpectrum6676.graph DegreeTwoThreeSpectrum5544.graph
    sourceMap5273 fusedMap5273 sourceMap5273_checked fusedMap5273_checked
    DegreeTwoThreeFiniteComparisons.comparison5273
#print axioms sourceMap5273_checked
#print axioms fusedMap5273_checked
#print axioms certified5273
def sourceMap5273swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,12,13,14,15,16,9,10,11] (sourceLabel 7 5 2 v)
def fusedMap5273swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5273swap_checked : acceptsGraphIso
    (source (graph core5273) (root 7) 5 2) DegreeTwoThreeSpectrum6676.graph sourceMap5273swap=true := by decide +kernel
theorem fusedMap5273swap_checked : acceptsGraphIso
    (fused (graph core5273) (root 7) 5 2) DegreeTwoThreeSpectrum5544.graph fusedMap5273swap=true := by decide +kernel
theorem certified5273swap : Certified (graph core5273) (root 7) 5 2 :=
  of_native_maps core5273 DegreeTwoThreeSpectrum6676.graph DegreeTwoThreeSpectrum5544.graph
    sourceMap5273swap fusedMap5273swap sourceMap5273swap_checked fusedMap5273swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5273
#print axioms sourceMap5273swap_checked
#print axioms fusedMap5273swap_checked
#print axioms certified5273swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
