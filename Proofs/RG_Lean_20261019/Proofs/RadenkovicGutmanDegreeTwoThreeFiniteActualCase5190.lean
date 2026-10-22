/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5190 : Family 8 := level8.get ⟨211,by decide⟩
def sourceMap5190 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5190 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5190_checked : acceptsGraphIso
    (source (graph core5190) (root 8) 2 4) DegreeTwoThreeSpectrum7189.graph sourceMap5190=true := by decide +kernel
theorem fusedMap5190_checked : acceptsGraphIso
    (fused (graph core5190) (root 8) 2 4) DegreeTwoThreeSpectrum5229.graph fusedMap5190=true := by decide +kernel
theorem certified5190 : Certified (graph core5190) (root 8) 2 4 :=
  of_native_maps core5190 DegreeTwoThreeSpectrum7189.graph DegreeTwoThreeSpectrum5229.graph
    sourceMap5190 fusedMap5190 sourceMap5190_checked fusedMap5190_checked
    DegreeTwoThreeFiniteComparisons.comparison5190
#print axioms sourceMap5190_checked
#print axioms fusedMap5190_checked
#print axioms certified5190
def sourceMap5190swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5190swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5190swap_checked : acceptsGraphIso
    (source (graph core5190) (root 8) 4 2) DegreeTwoThreeSpectrum7189.graph sourceMap5190swap=true := by decide +kernel
theorem fusedMap5190swap_checked : acceptsGraphIso
    (fused (graph core5190) (root 8) 4 2) DegreeTwoThreeSpectrum5229.graph fusedMap5190swap=true := by decide +kernel
theorem certified5190swap : Certified (graph core5190) (root 8) 4 2 :=
  of_native_maps core5190 DegreeTwoThreeSpectrum7189.graph DegreeTwoThreeSpectrum5229.graph
    sourceMap5190swap fusedMap5190swap sourceMap5190swap_checked fusedMap5190swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5190
#print axioms sourceMap5190swap_checked
#print axioms fusedMap5190swap_checked
#print axioms certified5190swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
