/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5292 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap5292 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5292 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5292_checked : acceptsGraphIso
    (source (graph core5292) (root 6) 2 6) DegreeTwoThreeSpectrum5599.graph sourceMap5292=true := by decide +kernel
theorem fusedMap5292_checked : acceptsGraphIso
    (fused (graph core5292) (root 6) 2 6) DegreeTwoThreeSpectrum5033.graph fusedMap5292=true := by decide +kernel
theorem certified5292 : Certified (graph core5292) (root 6) 2 6 :=
  of_native_maps core5292 DegreeTwoThreeSpectrum5599.graph DegreeTwoThreeSpectrum5033.graph
    sourceMap5292 fusedMap5292 sourceMap5292_checked fusedMap5292_checked
    DegreeTwoThreeFiniteComparisons.comparison5292
#print axioms sourceMap5292_checked
#print axioms fusedMap5292_checked
#print axioms certified5292
def sourceMap5292swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,16,7,8,9] (sourceLabel 6 6 2 v)
def fusedMap5292swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5292swap_checked : acceptsGraphIso
    (source (graph core5292) (root 6) 6 2) DegreeTwoThreeSpectrum5599.graph sourceMap5292swap=true := by decide +kernel
theorem fusedMap5292swap_checked : acceptsGraphIso
    (fused (graph core5292) (root 6) 6 2) DegreeTwoThreeSpectrum5033.graph fusedMap5292swap=true := by decide +kernel
theorem certified5292swap : Certified (graph core5292) (root 6) 6 2 :=
  of_native_maps core5292 DegreeTwoThreeSpectrum5599.graph DegreeTwoThreeSpectrum5033.graph
    sourceMap5292swap fusedMap5292swap sourceMap5292swap_checked fusedMap5292swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5292
#print axioms sourceMap5292swap_checked
#print axioms fusedMap5292swap_checked
#print axioms certified5292swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
