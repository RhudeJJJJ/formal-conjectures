/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5422 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5422 : (Vertices 2 ⊕ Fin 6 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,7,8,1,2,3,4,5,6,9,10,11,12,13,14,15] (sourceLabel 2 5 6 v)
def fusedMap5422 : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 5 6 v)
theorem sourceMap5422_checked : acceptsGraphIso
    (source (graph core5422) (root 2) 5 6) DegreeTwoThreeSpectrum3889.graph sourceMap5422=true := by decide +kernel
theorem fusedMap5422_checked : acceptsGraphIso
    (fused (graph core5422) (root 2) 5 6) DegreeTwoThreeSpectrum3861.graph fusedMap5422=true := by decide +kernel
theorem certified5422 : Certified (graph core5422) (root 2) 5 6 :=
  of_native_maps core5422 DegreeTwoThreeSpectrum3889.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap5422 fusedMap5422 sourceMap5422_checked fusedMap5422_checked
    DegreeTwoThreeFiniteComparisons.comparison5422
#print axioms sourceMap5422_checked
#print axioms fusedMap5422_checked
#print axioms certified5422
def sourceMap5422swap : (Vertices 2 ⊕ Fin 7 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 2 6 5 v)
def fusedMap5422swap : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 6 5 v)
theorem sourceMap5422swap_checked : acceptsGraphIso
    (source (graph core5422) (root 2) 6 5) DegreeTwoThreeSpectrum3889.graph sourceMap5422swap=true := by decide +kernel
theorem fusedMap5422swap_checked : acceptsGraphIso
    (fused (graph core5422) (root 2) 6 5) DegreeTwoThreeSpectrum3861.graph fusedMap5422swap=true := by decide +kernel
theorem certified5422swap : Certified (graph core5422) (root 2) 6 5 :=
  of_native_maps core5422 DegreeTwoThreeSpectrum3889.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap5422swap fusedMap5422swap sourceMap5422swap_checked fusedMap5422swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5422
#print axioms sourceMap5422swap_checked
#print axioms fusedMap5422swap_checked
#print axioms certified5422swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
