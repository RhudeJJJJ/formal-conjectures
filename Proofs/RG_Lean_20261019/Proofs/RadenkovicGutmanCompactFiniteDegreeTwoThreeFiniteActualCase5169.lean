/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5169 : Family 8 := level8.get ⟨162,by decide⟩
def sourceMap5169 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5169 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5169_checked : acceptsGraphIso
    (source (graph core5169) (root 8) 2 4) DegreeTwoThreeSpectrum6858.graph sourceMap5169=true := by decide +kernel
theorem fusedMap5169_checked : acceptsGraphIso
    (fused (graph core5169) (root 8) 2 4) DegreeTwoThreeSpectrum5665.graph fusedMap5169=true := by decide +kernel
theorem certified5169 : Certified (graph core5169) (root 8) 2 4 :=
  of_native_maps core5169 DegreeTwoThreeSpectrum6858.graph DegreeTwoThreeSpectrum5665.graph
    sourceMap5169 fusedMap5169 sourceMap5169_checked fusedMap5169_checked
    DegreeTwoThreeFiniteComparisons.comparison5169
#print axioms sourceMap5169_checked
#print axioms fusedMap5169_checked
#print axioms certified5169
def sourceMap5169swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5169swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5169swap_checked : acceptsGraphIso
    (source (graph core5169) (root 8) 4 2) DegreeTwoThreeSpectrum6858.graph sourceMap5169swap=true := by decide +kernel
theorem fusedMap5169swap_checked : acceptsGraphIso
    (fused (graph core5169) (root 8) 4 2) DegreeTwoThreeSpectrum5665.graph fusedMap5169swap=true := by decide +kernel
theorem certified5169swap : Certified (graph core5169) (root 8) 4 2 :=
  of_native_maps core5169 DegreeTwoThreeSpectrum6858.graph DegreeTwoThreeSpectrum5665.graph
    sourceMap5169swap fusedMap5169swap sourceMap5169swap_checked fusedMap5169swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5169
#print axioms sourceMap5169swap_checked
#print axioms fusedMap5169swap_checked
#print axioms certified5169swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
