/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5337 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap5337 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,10,6,7,8,9,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5337 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5337_checked : acceptsGraphIso
    (source (graph core5337) (root 6) 3 4) DegreeTwoThreeSpectrum4368.graph sourceMap5337=true := by decide +kernel
theorem fusedMap5337_checked : acceptsGraphIso
    (fused (graph core5337) (root 6) 3 4) DegreeTwoThreeSpectrum3857.graph fusedMap5337=true := by decide +kernel
theorem certified5337 : Certified (graph core5337) (root 6) 3 4 :=
  of_native_maps core5337 DegreeTwoThreeSpectrum4368.graph DegreeTwoThreeSpectrum3857.graph
    sourceMap5337 fusedMap5337 sourceMap5337_checked fusedMap5337_checked
    DegreeTwoThreeFiniteComparisons.comparison5337
#print axioms sourceMap5337_checked
#print axioms fusedMap5337_checked
#print axioms certified5337
def sourceMap5337swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,15,6,7,8,9] (sourceLabel 6 4 3 v)
def fusedMap5337swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5337swap_checked : acceptsGraphIso
    (source (graph core5337) (root 6) 4 3) DegreeTwoThreeSpectrum4368.graph sourceMap5337swap=true := by decide +kernel
theorem fusedMap5337swap_checked : acceptsGraphIso
    (fused (graph core5337) (root 6) 4 3) DegreeTwoThreeSpectrum3857.graph fusedMap5337swap=true := by decide +kernel
theorem certified5337swap : Certified (graph core5337) (root 6) 4 3 :=
  of_native_maps core5337 DegreeTwoThreeSpectrum4368.graph DegreeTwoThreeSpectrum3857.graph
    sourceMap5337swap fusedMap5337swap sourceMap5337swap_checked fusedMap5337swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5337
#print axioms sourceMap5337swap_checked
#print axioms fusedMap5337swap_checked
#print axioms certified5337swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
