/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5174 : Family 8 := level8.get ⟨173,by decide⟩
def sourceMap5174 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5174 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5174_checked : acceptsGraphIso
    (source (graph core5174) (root 8) 2 4) DegreeTwoThreeSpectrum6950.graph sourceMap5174=true := by decide +kernel
theorem fusedMap5174_checked : acceptsGraphIso
    (fused (graph core5174) (root 8) 2 4) DegreeTwoThreeSpectrum5741.graph fusedMap5174=true := by decide +kernel
theorem certified5174 : Certified (graph core5174) (root 8) 2 4 :=
  of_native_maps core5174 DegreeTwoThreeSpectrum6950.graph DegreeTwoThreeSpectrum5741.graph
    sourceMap5174 fusedMap5174 sourceMap5174_checked fusedMap5174_checked
    DegreeTwoThreeFiniteComparisons.comparison5174
#print axioms sourceMap5174_checked
#print axioms fusedMap5174_checked
#print axioms certified5174
def sourceMap5174swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5174swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5174swap_checked : acceptsGraphIso
    (source (graph core5174) (root 8) 4 2) DegreeTwoThreeSpectrum6950.graph sourceMap5174swap=true := by decide +kernel
theorem fusedMap5174swap_checked : acceptsGraphIso
    (fused (graph core5174) (root 8) 4 2) DegreeTwoThreeSpectrum5741.graph fusedMap5174swap=true := by decide +kernel
theorem certified5174swap : Certified (graph core5174) (root 8) 4 2 :=
  of_native_maps core5174 DegreeTwoThreeSpectrum6950.graph DegreeTwoThreeSpectrum5741.graph
    sourceMap5174swap fusedMap5174swap sourceMap5174swap_checked fusedMap5174swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5174
#print axioms sourceMap5174swap_checked
#print axioms fusedMap5174swap_checked
#print axioms certified5174swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
