/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5065 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap5065 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,5,6,7,8,9,2,3,4,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap5065 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap5065_checked : acceptsGraphIso
    (source (graph core5065) (root 5) 2 4) DegreeTwoThreeSpectrum2196.graph sourceMap5065=true := by decide +kernel
theorem fusedMap5065_checked : acceptsGraphIso
    (fused (graph core5065) (root 5) 2 4) DegreeTwoThreeSpectrum1761.graph fusedMap5065=true := by decide +kernel
theorem certified5065 : Certified (graph core5065) (root 5) 2 4 :=
  of_native_maps core5065 DegreeTwoThreeSpectrum2196.graph DegreeTwoThreeSpectrum1761.graph
    sourceMap5065 fusedMap5065 sourceMap5065_checked fusedMap5065_checked
    DegreeTwoThreeFiniteComparisons.comparison5065
#print axioms sourceMap5065_checked
#print axioms fusedMap5065_checked
#print axioms certified5065
def sourceMap5065swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,5,6,7,8,9,0,10,11,12,13,2,3,4] (sourceLabel 5 4 2 v)
def fusedMap5065swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap5065swap_checked : acceptsGraphIso
    (source (graph core5065) (root 5) 4 2) DegreeTwoThreeSpectrum2196.graph sourceMap5065swap=true := by decide +kernel
theorem fusedMap5065swap_checked : acceptsGraphIso
    (fused (graph core5065) (root 5) 4 2) DegreeTwoThreeSpectrum1761.graph fusedMap5065swap=true := by decide +kernel
theorem certified5065swap : Certified (graph core5065) (root 5) 4 2 :=
  of_native_maps core5065 DegreeTwoThreeSpectrum2196.graph DegreeTwoThreeSpectrum1761.graph
    sourceMap5065swap fusedMap5065swap sourceMap5065swap_checked fusedMap5065swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5065
#print axioms sourceMap5065swap_checked
#print axioms fusedMap5065swap_checked
#print axioms certified5065swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
