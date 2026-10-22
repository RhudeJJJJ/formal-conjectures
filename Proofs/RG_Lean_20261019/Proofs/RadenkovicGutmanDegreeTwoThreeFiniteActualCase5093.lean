/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5093 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap5093 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5093 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5093_checked : acceptsGraphIso
    (source (graph core5093) (root 7) 2 4) DegreeTwoThreeSpectrum4472.graph sourceMap5093=true := by decide +kernel
theorem fusedMap5093_checked : acceptsGraphIso
    (fused (graph core5093) (root 7) 2 4) DegreeTwoThreeSpectrum4012.graph fusedMap5093=true := by decide +kernel
theorem certified5093 : Certified (graph core5093) (root 7) 2 4 :=
  of_native_maps core5093 DegreeTwoThreeSpectrum4472.graph DegreeTwoThreeSpectrum4012.graph
    sourceMap5093 fusedMap5093 sourceMap5093_checked fusedMap5093_checked
    DegreeTwoThreeFiniteComparisons.comparison5093
#print axioms sourceMap5093_checked
#print axioms fusedMap5093_checked
#print axioms certified5093
def sourceMap5093swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5093swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5093swap_checked : acceptsGraphIso
    (source (graph core5093) (root 7) 4 2) DegreeTwoThreeSpectrum4472.graph sourceMap5093swap=true := by decide +kernel
theorem fusedMap5093swap_checked : acceptsGraphIso
    (fused (graph core5093) (root 7) 4 2) DegreeTwoThreeSpectrum4012.graph fusedMap5093swap=true := by decide +kernel
theorem certified5093swap : Certified (graph core5093) (root 7) 4 2 :=
  of_native_maps core5093 DegreeTwoThreeSpectrum4472.graph DegreeTwoThreeSpectrum4012.graph
    sourceMap5093swap fusedMap5093swap sourceMap5093swap_checked fusedMap5093swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5093
#print axioms sourceMap5093swap_checked
#print axioms fusedMap5093swap_checked
#print axioms certified5093swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
