/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5090 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap5090 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5090 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5090_checked : acceptsGraphIso
    (source (graph core5090) (root 7) 2 4) DegreeTwoThreeSpectrum4359.graph sourceMap5090=true := by decide +kernel
theorem fusedMap5090_checked : acceptsGraphIso
    (fused (graph core5090) (root 7) 2 4) DegreeTwoThreeSpectrum3953.graph fusedMap5090=true := by decide +kernel
theorem certified5090 : Certified (graph core5090) (root 7) 2 4 :=
  of_native_maps core5090 DegreeTwoThreeSpectrum4359.graph DegreeTwoThreeSpectrum3953.graph
    sourceMap5090 fusedMap5090 sourceMap5090_checked fusedMap5090_checked
    DegreeTwoThreeFiniteComparisons.comparison5090
#print axioms sourceMap5090_checked
#print axioms fusedMap5090_checked
#print axioms certified5090
def sourceMap5090swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5090swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5090swap_checked : acceptsGraphIso
    (source (graph core5090) (root 7) 4 2) DegreeTwoThreeSpectrum4359.graph sourceMap5090swap=true := by decide +kernel
theorem fusedMap5090swap_checked : acceptsGraphIso
    (fused (graph core5090) (root 7) 4 2) DegreeTwoThreeSpectrum3953.graph fusedMap5090swap=true := by decide +kernel
theorem certified5090swap : Certified (graph core5090) (root 7) 4 2 :=
  of_native_maps core5090 DegreeTwoThreeSpectrum4359.graph DegreeTwoThreeSpectrum3953.graph
    sourceMap5090swap fusedMap5090swap sourceMap5090swap_checked fusedMap5090swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5090
#print axioms sourceMap5090swap_checked
#print axioms fusedMap5090swap_checked
#print axioms certified5090swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
