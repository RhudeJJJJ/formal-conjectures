/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5230 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap5230 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,6,7,8,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5230 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5230_checked : acceptsGraphIso
    (source (graph core5230) (root 6) 2 5) DegreeTwoThreeSpectrum4642.graph sourceMap5230=true := by decide +kernel
theorem fusedMap5230_checked : acceptsGraphIso
    (fused (graph core5230) (root 6) 2 5) DegreeTwoThreeSpectrum3877.graph fusedMap5230=true := by decide +kernel
theorem certified5230 : Certified (graph core5230) (root 6) 2 5 :=
  of_native_maps core5230 DegreeTwoThreeSpectrum4642.graph DegreeTwoThreeSpectrum3877.graph
    sourceMap5230 fusedMap5230 sourceMap5230_checked fusedMap5230_checked
    DegreeTwoThreeFiniteComparisons.comparison5230
#print axioms sourceMap5230_checked
#print axioms fusedMap5230_checked
#print axioms certified5230
def sourceMap5230swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,0,11,12,13,14,15,6,7,8] (sourceLabel 6 5 2 v)
def fusedMap5230swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5230swap_checked : acceptsGraphIso
    (source (graph core5230) (root 6) 5 2) DegreeTwoThreeSpectrum4642.graph sourceMap5230swap=true := by decide +kernel
theorem fusedMap5230swap_checked : acceptsGraphIso
    (fused (graph core5230) (root 6) 5 2) DegreeTwoThreeSpectrum3877.graph fusedMap5230swap=true := by decide +kernel
theorem certified5230swap : Certified (graph core5230) (root 6) 5 2 :=
  of_native_maps core5230 DegreeTwoThreeSpectrum4642.graph DegreeTwoThreeSpectrum3877.graph
    sourceMap5230swap fusedMap5230swap sourceMap5230swap_checked fusedMap5230swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5230
#print axioms sourceMap5230swap_checked
#print axioms fusedMap5230swap_checked
#print axioms certified5230swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
