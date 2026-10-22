/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5208 : Family 8 := level8.get ⟨248,by decide⟩
def sourceMap5208 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5208 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5208_checked : acceptsGraphIso
    (source (graph core5208) (root 8) 2 4) DegreeTwoThreeSpectrum7424.graph sourceMap5208=true := by decide +kernel
theorem fusedMap5208_checked : acceptsGraphIso
    (fused (graph core5208) (root 8) 2 4) DegreeTwoThreeSpectrum5540.graph fusedMap5208=true := by decide +kernel
theorem certified5208 : Certified (graph core5208) (root 8) 2 4 :=
  of_native_maps core5208 DegreeTwoThreeSpectrum7424.graph DegreeTwoThreeSpectrum5540.graph
    sourceMap5208 fusedMap5208 sourceMap5208_checked fusedMap5208_checked
    DegreeTwoThreeFiniteComparisons.comparison5208
#print axioms sourceMap5208_checked
#print axioms fusedMap5208_checked
#print axioms certified5208
def sourceMap5208swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,13,14,15,16,10,11,12] (sourceLabel 8 4 2 v)
def fusedMap5208swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5208swap_checked : acceptsGraphIso
    (source (graph core5208) (root 8) 4 2) DegreeTwoThreeSpectrum7424.graph sourceMap5208swap=true := by decide +kernel
theorem fusedMap5208swap_checked : acceptsGraphIso
    (fused (graph core5208) (root 8) 4 2) DegreeTwoThreeSpectrum5540.graph fusedMap5208swap=true := by decide +kernel
theorem certified5208swap : Certified (graph core5208) (root 8) 4 2 :=
  of_native_maps core5208 DegreeTwoThreeSpectrum7424.graph DegreeTwoThreeSpectrum5540.graph
    sourceMap5208swap fusedMap5208swap sourceMap5208swap_checked fusedMap5208swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5208
#print axioms sourceMap5208swap_checked
#print axioms fusedMap5208swap_checked
#print axioms certified5208swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
