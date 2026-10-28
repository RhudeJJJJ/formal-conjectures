/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5146 : Family 8 := level8.get ⟨102,by decide⟩
def sourceMap5146 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5146 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5146_checked : acceptsGraphIso
    (source (graph core5146) (root 8) 2 4) DegreeTwoThreeSpectrum6106.graph sourceMap5146=true := by decide +kernel
theorem fusedMap5146_checked : acceptsGraphIso
    (fused (graph core5146) (root 8) 2 4) DegreeTwoThreeSpectrum5177.graph fusedMap5146=true := by decide +kernel
theorem certified5146 : Certified (graph core5146) (root 8) 2 4 :=
  of_native_maps core5146 DegreeTwoThreeSpectrum6106.graph DegreeTwoThreeSpectrum5177.graph
    sourceMap5146 fusedMap5146 sourceMap5146_checked fusedMap5146_checked
    DegreeTwoThreeFiniteComparisons.comparison5146
#print axioms sourceMap5146_checked
#print axioms fusedMap5146_checked
#print axioms certified5146
def sourceMap5146swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5146swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5146swap_checked : acceptsGraphIso
    (source (graph core5146) (root 8) 4 2) DegreeTwoThreeSpectrum6106.graph sourceMap5146swap=true := by decide +kernel
theorem fusedMap5146swap_checked : acceptsGraphIso
    (fused (graph core5146) (root 8) 4 2) DegreeTwoThreeSpectrum5177.graph fusedMap5146swap=true := by decide +kernel
theorem certified5146swap : Certified (graph core5146) (root 8) 4 2 :=
  of_native_maps core5146 DegreeTwoThreeSpectrum6106.graph DegreeTwoThreeSpectrum5177.graph
    sourceMap5146swap fusedMap5146swap sourceMap5146swap_checked fusedMap5146swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5146
#print axioms sourceMap5146swap_checked
#print axioms fusedMap5146swap_checked
#print axioms certified5146swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
