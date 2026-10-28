/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5313 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap5313 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,7,8,9,1,0,11,12,13,14,15,16] (sourceLabel 5 2 7 v)
def fusedMap5313 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 2 7 v)
theorem sourceMap5313_checked : acceptsGraphIso
    (source (graph core5313) (root 5) 2 7) DegreeTwoThreeSpectrum5541.graph sourceMap5313=true := by decide +kernel
theorem fusedMap5313_checked : acceptsGraphIso
    (fused (graph core5313) (root 5) 2 7) DegreeTwoThreeSpectrum5027.graph fusedMap5313=true := by decide +kernel
theorem certified5313 : Certified (graph core5313) (root 5) 2 7 :=
  of_native_maps core5313 DegreeTwoThreeSpectrum5541.graph DegreeTwoThreeSpectrum5027.graph
    sourceMap5313 fusedMap5313 sourceMap5313_checked fusedMap5313_checked
    DegreeTwoThreeFiniteComparisons.comparison5313
#print axioms sourceMap5313_checked
#print axioms fusedMap5313_checked
#print axioms certified5313
def sourceMap5313swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,1,0,11,12,13,14,15,16,7,8,9] (sourceLabel 5 7 2 v)
def fusedMap5313swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 7 2 v)
theorem sourceMap5313swap_checked : acceptsGraphIso
    (source (graph core5313) (root 5) 7 2) DegreeTwoThreeSpectrum5541.graph sourceMap5313swap=true := by decide +kernel
theorem fusedMap5313swap_checked : acceptsGraphIso
    (fused (graph core5313) (root 5) 7 2) DegreeTwoThreeSpectrum5027.graph fusedMap5313swap=true := by decide +kernel
theorem certified5313swap : Certified (graph core5313) (root 5) 7 2 :=
  of_native_maps core5313 DegreeTwoThreeSpectrum5541.graph DegreeTwoThreeSpectrum5027.graph
    sourceMap5313swap fusedMap5313swap sourceMap5313swap_checked fusedMap5313swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5313
#print axioms sourceMap5313swap_checked
#print axioms fusedMap5313swap_checked
#print axioms certified5313swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
