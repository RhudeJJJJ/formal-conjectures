/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5186 : Family 8 := level8.get ⟨201,by decide⟩
def sourceMap5186 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,8,9,10,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5186 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5186_checked : acceptsGraphIso
    (source (graph core5186) (root 8) 2 4) DegreeTwoThreeSpectrum7133.graph sourceMap5186=true := by decide +kernel
theorem fusedMap5186_checked : acceptsGraphIso
    (fused (graph core5186) (root 8) 2 4) DegreeTwoThreeSpectrum5169.graph fusedMap5186=true := by decide +kernel
theorem certified5186 : Certified (graph core5186) (root 8) 2 4 :=
  of_native_maps core5186 DegreeTwoThreeSpectrum7133.graph DegreeTwoThreeSpectrum5169.graph
    sourceMap5186 fusedMap5186 sourceMap5186_checked fusedMap5186_checked
    DegreeTwoThreeFiniteComparisons.comparison5186
#print axioms sourceMap5186_checked
#print axioms fusedMap5186_checked
#print axioms certified5186
def sourceMap5186swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,0,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5186swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5186swap_checked : acceptsGraphIso
    (source (graph core5186) (root 8) 4 2) DegreeTwoThreeSpectrum7133.graph sourceMap5186swap=true := by decide +kernel
theorem fusedMap5186swap_checked : acceptsGraphIso
    (fused (graph core5186) (root 8) 4 2) DegreeTwoThreeSpectrum5169.graph fusedMap5186swap=true := by decide +kernel
theorem certified5186swap : Certified (graph core5186) (root 8) 4 2 :=
  of_native_maps core5186 DegreeTwoThreeSpectrum7133.graph DegreeTwoThreeSpectrum5169.graph
    sourceMap5186swap fusedMap5186swap sourceMap5186swap_checked fusedMap5186swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5186
#print axioms sourceMap5186swap_checked
#print axioms fusedMap5186swap_checked
#print axioms certified5186swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
