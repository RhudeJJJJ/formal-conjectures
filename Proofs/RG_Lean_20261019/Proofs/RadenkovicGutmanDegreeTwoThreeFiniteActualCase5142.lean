/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5142 : Family 8 := level8.get ⟨89,by decide⟩
def sourceMap5142 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,15,16,12,13,14,7,8,9,10,11] (sourceLabel 8 2 4 v)
def fusedMap5142 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5142_checked : acceptsGraphIso
    (source (graph core5142) (root 8) 2 4) DegreeTwoThreeSpectrum7039.graph sourceMap5142=true := by decide +kernel
theorem fusedMap5142_checked : acceptsGraphIso
    (fused (graph core5142) (root 8) 2 4) DegreeTwoThreeSpectrum5092.graph fusedMap5142=true := by decide +kernel
theorem certified5142 : Certified (graph core5142) (root 8) 2 4 :=
  of_native_maps core5142 DegreeTwoThreeSpectrum7039.graph DegreeTwoThreeSpectrum5092.graph
    sourceMap5142 fusedMap5142 sourceMap5142_checked fusedMap5142_checked
    DegreeTwoThreeFiniteComparisons.comparison5142
#print axioms sourceMap5142_checked
#print axioms fusedMap5142_checked
#print axioms certified5142
def sourceMap5142swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,15,16,7,8,9,10,11,12,13,14] (sourceLabel 8 4 2 v)
def fusedMap5142swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5142swap_checked : acceptsGraphIso
    (source (graph core5142) (root 8) 4 2) DegreeTwoThreeSpectrum7039.graph sourceMap5142swap=true := by decide +kernel
theorem fusedMap5142swap_checked : acceptsGraphIso
    (fused (graph core5142) (root 8) 4 2) DegreeTwoThreeSpectrum5092.graph fusedMap5142swap=true := by decide +kernel
theorem certified5142swap : Certified (graph core5142) (root 8) 4 2 :=
  of_native_maps core5142 DegreeTwoThreeSpectrum7039.graph DegreeTwoThreeSpectrum5092.graph
    sourceMap5142swap fusedMap5142swap sourceMap5142swap_checked fusedMap5142swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5142
#print axioms sourceMap5142swap_checked
#print axioms fusedMap5142swap_checked
#print axioms certified5142swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
