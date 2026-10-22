/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5182 : Family 8 := level8.get ⟨193,by decide⟩
def sourceMap5182 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5182 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5182_checked : acceptsGraphIso
    (source (graph core5182) (root 8) 2 4) DegreeTwoThreeSpectrum7091.graph sourceMap5182=true := by decide +kernel
theorem fusedMap5182_checked : acceptsGraphIso
    (fused (graph core5182) (root 8) 2 4) DegreeTwoThreeSpectrum5141.graph fusedMap5182=true := by decide +kernel
theorem certified5182 : Certified (graph core5182) (root 8) 2 4 :=
  of_native_maps core5182 DegreeTwoThreeSpectrum7091.graph DegreeTwoThreeSpectrum5141.graph
    sourceMap5182 fusedMap5182 sourceMap5182_checked fusedMap5182_checked
    DegreeTwoThreeFiniteComparisons.comparison5182
#print axioms sourceMap5182_checked
#print axioms fusedMap5182_checked
#print axioms certified5182
def sourceMap5182swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5182swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5182swap_checked : acceptsGraphIso
    (source (graph core5182) (root 8) 4 2) DegreeTwoThreeSpectrum7091.graph sourceMap5182swap=true := by decide +kernel
theorem fusedMap5182swap_checked : acceptsGraphIso
    (fused (graph core5182) (root 8) 4 2) DegreeTwoThreeSpectrum5141.graph fusedMap5182swap=true := by decide +kernel
theorem certified5182swap : Certified (graph core5182) (root 8) 4 2 :=
  of_native_maps core5182 DegreeTwoThreeSpectrum7091.graph DegreeTwoThreeSpectrum5141.graph
    sourceMap5182swap fusedMap5182swap sourceMap5182swap_checked fusedMap5182swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5182
#print axioms sourceMap5182swap_checked
#print axioms fusedMap5182swap_checked
#print axioms certified5182swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
