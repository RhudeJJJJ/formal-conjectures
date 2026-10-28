/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5087 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap5087 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,14,15,11,12,13,6,7,8,9,10] (sourceLabel 7 2 4 v)
def fusedMap5087 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5087_checked : acceptsGraphIso
    (source (graph core5087) (root 7) 2 4) DegreeTwoThreeSpectrum4661.graph sourceMap5087=true := by decide +kernel
theorem fusedMap5087_checked : acceptsGraphIso
    (fused (graph core5087) (root 7) 2 4) DegreeTwoThreeSpectrum3883.graph fusedMap5087=true := by decide +kernel
theorem certified5087 : Certified (graph core5087) (root 7) 2 4 :=
  of_native_maps core5087 DegreeTwoThreeSpectrum4661.graph DegreeTwoThreeSpectrum3883.graph
    sourceMap5087 fusedMap5087 sourceMap5087_checked fusedMap5087_checked
    DegreeTwoThreeFiniteComparisons.comparison5087
#print axioms sourceMap5087_checked
#print axioms fusedMap5087_checked
#print axioms certified5087
def sourceMap5087swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,14,15,6,7,8,9,10,11,12,13] (sourceLabel 7 4 2 v)
def fusedMap5087swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5087swap_checked : acceptsGraphIso
    (source (graph core5087) (root 7) 4 2) DegreeTwoThreeSpectrum4661.graph sourceMap5087swap=true := by decide +kernel
theorem fusedMap5087swap_checked : acceptsGraphIso
    (fused (graph core5087) (root 7) 4 2) DegreeTwoThreeSpectrum3883.graph fusedMap5087swap=true := by decide +kernel
theorem certified5087swap : Certified (graph core5087) (root 7) 4 2 :=
  of_native_maps core5087 DegreeTwoThreeSpectrum4661.graph DegreeTwoThreeSpectrum3883.graph
    sourceMap5087swap fusedMap5087swap sourceMap5087swap_checked fusedMap5087swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5087
#print axioms sourceMap5087swap_checked
#print axioms fusedMap5087swap_checked
#print axioms certified5087swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
