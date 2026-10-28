/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5096 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap5096 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9,11,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5096 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5096_checked : acceptsGraphIso
    (source (graph core5096) (root 7) 2 4) DegreeTwoThreeSpectrum4585.graph sourceMap5096=true := by decide +kernel
theorem fusedMap5096_checked : acceptsGraphIso
    (fused (graph core5096) (root 7) 2 4) DegreeTwoThreeSpectrum4075.graph fusedMap5096=true := by decide +kernel
theorem certified5096 : Certified (graph core5096) (root 7) 2 4 :=
  of_native_maps core5096 DegreeTwoThreeSpectrum4585.graph DegreeTwoThreeSpectrum4075.graph
    sourceMap5096 fusedMap5096 sourceMap5096_checked fusedMap5096_checked
    DegreeTwoThreeFiniteComparisons.comparison5096
#print axioms sourceMap5096_checked
#print axioms fusedMap5096_checked
#print axioms certified5096
def sourceMap5096swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,7,8,9] (sourceLabel 7 4 2 v)
def fusedMap5096swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5096swap_checked : acceptsGraphIso
    (source (graph core5096) (root 7) 4 2) DegreeTwoThreeSpectrum4585.graph sourceMap5096swap=true := by decide +kernel
theorem fusedMap5096swap_checked : acceptsGraphIso
    (fused (graph core5096) (root 7) 4 2) DegreeTwoThreeSpectrum4075.graph fusedMap5096swap=true := by decide +kernel
theorem certified5096swap : Certified (graph core5096) (root 7) 4 2 :=
  of_native_maps core5096 DegreeTwoThreeSpectrum4585.graph DegreeTwoThreeSpectrum4075.graph
    sourceMap5096swap fusedMap5096swap sourceMap5096swap_checked fusedMap5096swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5096
#print axioms sourceMap5096swap_checked
#print axioms fusedMap5096swap_checked
#print axioms certified5096swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
