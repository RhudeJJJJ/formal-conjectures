/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5369 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5369 : (Vertices 3 ⊕ Fin 4 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,7,8,9,3,4,5,6,1,0,10,11,12,13,14,15] (sourceLabel 3 3 7 v)
def fusedMap5369 : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 3 7 v)
theorem sourceMap5369_checked : acceptsGraphIso
    (source (graph core5369) (root 3) 3 7) DegreeTwoThreeSpectrum4127.graph sourceMap5369=true := by decide +kernel
theorem fusedMap5369_checked : acceptsGraphIso
    (fused (graph core5369) (root 3) 3 7) DegreeTwoThreeSpectrum3869.graph fusedMap5369=true := by decide +kernel
theorem certified5369 : Certified (graph core5369) (root 3) 3 7 :=
  of_native_maps core5369 DegreeTwoThreeSpectrum4127.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap5369 fusedMap5369 sourceMap5369_checked fusedMap5369_checked
    DegreeTwoThreeFiniteComparisons.comparison5369
#print axioms sourceMap5369_checked
#print axioms fusedMap5369_checked
#print axioms certified5369
def sourceMap5369swap : (Vertices 3 ⊕ Fin 8 ⊕ Fin 4) → Fin 16 :=
  fun v => ![2,7,8,9,1,0,10,11,12,13,14,15,3,4,5,6] (sourceLabel 3 7 3 v)
def fusedMap5369swap : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 7 3 v)
theorem sourceMap5369swap_checked : acceptsGraphIso
    (source (graph core5369) (root 3) 7 3) DegreeTwoThreeSpectrum4127.graph sourceMap5369swap=true := by decide +kernel
theorem fusedMap5369swap_checked : acceptsGraphIso
    (fused (graph core5369) (root 3) 7 3) DegreeTwoThreeSpectrum3869.graph fusedMap5369swap=true := by decide +kernel
theorem certified5369swap : Certified (graph core5369) (root 3) 7 3 :=
  of_native_maps core5369 DegreeTwoThreeSpectrum4127.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap5369swap fusedMap5369swap sourceMap5369swap_checked fusedMap5369swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5369
#print axioms sourceMap5369swap_checked
#print axioms fusedMap5369swap_checked
#print axioms certified5369swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
