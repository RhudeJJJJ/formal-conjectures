/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5156 : Family 8 := level8.get ⟨128,by decide⟩
def sourceMap5156 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5156 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5156_checked : acceptsGraphIso
    (source (graph core5156) (root 8) 2 4) DegreeTwoThreeSpectrum6435.graph sourceMap5156=true := by decide +kernel
theorem fusedMap5156_checked : acceptsGraphIso
    (fused (graph core5156) (root 8) 2 4) DegreeTwoThreeSpectrum5367.graph fusedMap5156=true := by decide +kernel
theorem certified5156 : Certified (graph core5156) (root 8) 2 4 :=
  of_native_maps core5156 DegreeTwoThreeSpectrum6435.graph DegreeTwoThreeSpectrum5367.graph
    sourceMap5156 fusedMap5156 sourceMap5156_checked fusedMap5156_checked
    DegreeTwoThreeFiniteComparisons.comparison5156
#print axioms sourceMap5156_checked
#print axioms fusedMap5156_checked
#print axioms certified5156
def sourceMap5156swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5156swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5156swap_checked : acceptsGraphIso
    (source (graph core5156) (root 8) 4 2) DegreeTwoThreeSpectrum6435.graph sourceMap5156swap=true := by decide +kernel
theorem fusedMap5156swap_checked : acceptsGraphIso
    (fused (graph core5156) (root 8) 4 2) DegreeTwoThreeSpectrum5367.graph fusedMap5156swap=true := by decide +kernel
theorem certified5156swap : Certified (graph core5156) (root 8) 4 2 :=
  of_native_maps core5156 DegreeTwoThreeSpectrum6435.graph DegreeTwoThreeSpectrum5367.graph
    sourceMap5156swap fusedMap5156swap sourceMap5156swap_checked fusedMap5156swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5156
#print axioms sourceMap5156swap_checked
#print axioms fusedMap5156swap_checked
#print axioms certified5156swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
