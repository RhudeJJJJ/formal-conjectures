/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5229 : Family 6 := level6.get ⟨16,by decide⟩
def sourceMap5229 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5229 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5229_checked : acceptsGraphIso
    (source (graph core5229) (root 6) 2 5) DegreeTwoThreeSpectrum4614.graph sourceMap5229=true := by decide +kernel
theorem fusedMap5229_checked : acceptsGraphIso
    (fused (graph core5229) (root 6) 2 5) DegreeTwoThreeSpectrum3872.graph fusedMap5229=true := by decide +kernel
theorem certified5229 : Certified (graph core5229) (root 6) 2 5 :=
  of_native_maps core5229 DegreeTwoThreeSpectrum4614.graph DegreeTwoThreeSpectrum3872.graph
    sourceMap5229 fusedMap5229 sourceMap5229_checked fusedMap5229_checked
    DegreeTwoThreeFiniteComparisons.comparison5229
#print axioms sourceMap5229_checked
#print axioms fusedMap5229_checked
#print axioms certified5229
def sourceMap5229swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,7,8,9] (sourceLabel 6 5 2 v)
def fusedMap5229swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5229swap_checked : acceptsGraphIso
    (source (graph core5229) (root 6) 5 2) DegreeTwoThreeSpectrum4614.graph sourceMap5229swap=true := by decide +kernel
theorem fusedMap5229swap_checked : acceptsGraphIso
    (fused (graph core5229) (root 6) 5 2) DegreeTwoThreeSpectrum3872.graph fusedMap5229swap=true := by decide +kernel
theorem certified5229swap : Certified (graph core5229) (root 6) 5 2 :=
  of_native_maps core5229 DegreeTwoThreeSpectrum4614.graph DegreeTwoThreeSpectrum3872.graph
    sourceMap5229swap fusedMap5229swap sourceMap5229swap_checked fusedMap5229swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5229
#print axioms sourceMap5229swap_checked
#print axioms fusedMap5229swap_checked
#print axioms certified5229swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
