/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5357 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap5357 : (Vertices 5 ⊕ Fin 4 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,10,6,7,8,9,0,11,12,13,14,15] (sourceLabel 5 3 5 v)
def fusedMap5357 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 3 5 v)
theorem sourceMap5357_checked : acceptsGraphIso
    (source (graph core5357) (root 5) 3 5) DegreeTwoThreeSpectrum4627.graph sourceMap5357=true := by decide +kernel
theorem fusedMap5357_checked : acceptsGraphIso
    (fused (graph core5357) (root 5) 3 5) DegreeTwoThreeSpectrum3882.graph fusedMap5357=true := by decide +kernel
theorem certified5357 : Certified (graph core5357) (root 5) 3 5 :=
  of_native_maps core5357 DegreeTwoThreeSpectrum4627.graph DegreeTwoThreeSpectrum3882.graph
    sourceMap5357 fusedMap5357 sourceMap5357_checked fusedMap5357_checked
    DegreeTwoThreeFiniteComparisons.comparison5357
#print axioms sourceMap5357_checked
#print axioms fusedMap5357_checked
#print axioms certified5357
def sourceMap5357swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 4) → Fin 16 :=
  fun v => ![1,2,3,4,5,10,0,11,12,13,14,15,6,7,8,9] (sourceLabel 5 5 3 v)
def fusedMap5357swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 5 3 v)
theorem sourceMap5357swap_checked : acceptsGraphIso
    (source (graph core5357) (root 5) 5 3) DegreeTwoThreeSpectrum4627.graph sourceMap5357swap=true := by decide +kernel
theorem fusedMap5357swap_checked : acceptsGraphIso
    (fused (graph core5357) (root 5) 5 3) DegreeTwoThreeSpectrum3882.graph fusedMap5357swap=true := by decide +kernel
theorem certified5357swap : Certified (graph core5357) (root 5) 5 3 :=
  of_native_maps core5357 DegreeTwoThreeSpectrum4627.graph DegreeTwoThreeSpectrum3882.graph
    sourceMap5357swap fusedMap5357swap sourceMap5357swap_checked fusedMap5357swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5357
#print axioms sourceMap5357swap_checked
#print axioms fusedMap5357swap_checked
#print axioms certified5357swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
