/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5324 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5324 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,8,9,5,6,7,3,2,1,0,10,11,12,13,14,15,16] (sourceLabel 2 2 10 v)
def fusedMap5324 : (Vertices 2 ⊕ Fin 14) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 2 2 10 v)
theorem sourceMap5324_checked : acceptsGraphIso
    (source (graph core5324) (root 2) 2 10) DegreeTwoThreeSpectrum5060.graph sourceMap5324=true := by decide +kernel
theorem fusedMap5324_checked : acceptsGraphIso
    (fused (graph core5324) (root 2) 2 10) DegreeTwoThreeSpectrum4959.graph fusedMap5324=true := by decide +kernel
theorem certified5324 : Certified (graph core5324) (root 2) 2 10 :=
  of_native_maps core5324 DegreeTwoThreeSpectrum5060.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap5324 fusedMap5324 sourceMap5324_checked fusedMap5324_checked
    DegreeTwoThreeFiniteComparisons.comparison5324
#print axioms sourceMap5324_checked
#print axioms fusedMap5324_checked
#print axioms certified5324
def sourceMap5324swap : (Vertices 2 ⊕ Fin 11 ⊕ Fin 3) → Fin 17 :=
  fun v => ![4,8,9,3,2,1,0,10,11,12,13,14,15,16,5,6,7] (sourceLabel 2 10 2 v)
def fusedMap5324swap : (Vertices 2 ⊕ Fin 14) → Fin 17 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 2 10 2 v)
theorem sourceMap5324swap_checked : acceptsGraphIso
    (source (graph core5324) (root 2) 10 2) DegreeTwoThreeSpectrum5060.graph sourceMap5324swap=true := by decide +kernel
theorem fusedMap5324swap_checked : acceptsGraphIso
    (fused (graph core5324) (root 2) 10 2) DegreeTwoThreeSpectrum4959.graph fusedMap5324swap=true := by decide +kernel
theorem certified5324swap : Certified (graph core5324) (root 2) 10 2 :=
  of_native_maps core5324 DegreeTwoThreeSpectrum5060.graph DegreeTwoThreeSpectrum4959.graph
    sourceMap5324swap fusedMap5324swap sourceMap5324swap_checked fusedMap5324swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5324
#print axioms sourceMap5324swap_checked
#print axioms fusedMap5324swap_checked
#print axioms certified5324swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
