/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5347 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap5347 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5347 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5347_checked : acceptsGraphIso
    (source (graph core5347) (root 6) 3 4) DegreeTwoThreeSpectrum4640.graph sourceMap5347=true := by decide +kernel
theorem fusedMap5347_checked : acceptsGraphIso
    (fused (graph core5347) (root 6) 3 4) DegreeTwoThreeSpectrum4062.graph fusedMap5347=true := by decide +kernel
theorem certified5347 : Certified (graph core5347) (root 6) 3 4 :=
  of_native_maps core5347 DegreeTwoThreeSpectrum4640.graph DegreeTwoThreeSpectrum4062.graph
    sourceMap5347 fusedMap5347 sourceMap5347_checked fusedMap5347_checked
    DegreeTwoThreeFiniteComparisons.comparison5347
#print axioms sourceMap5347_checked
#print axioms fusedMap5347_checked
#print axioms certified5347
def sourceMap5347swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5347swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5347swap_checked : acceptsGraphIso
    (source (graph core5347) (root 6) 4 3) DegreeTwoThreeSpectrum4640.graph sourceMap5347swap=true := by decide +kernel
theorem fusedMap5347swap_checked : acceptsGraphIso
    (fused (graph core5347) (root 6) 4 3) DegreeTwoThreeSpectrum4062.graph fusedMap5347swap=true := by decide +kernel
theorem certified5347swap : Certified (graph core5347) (root 6) 4 3 :=
  of_native_maps core5347 DegreeTwoThreeSpectrum4640.graph DegreeTwoThreeSpectrum4062.graph
    sourceMap5347swap fusedMap5347swap sourceMap5347swap_checked fusedMap5347swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5347
#print axioms sourceMap5347swap_checked
#print axioms fusedMap5347swap_checked
#print axioms certified5347swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
