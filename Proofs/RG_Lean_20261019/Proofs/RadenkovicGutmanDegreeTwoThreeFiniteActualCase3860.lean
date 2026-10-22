/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3860 : Family 8 := level8.get ⟨118,by decide⟩
def sourceMap3860 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3860 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3860_checked : acceptsGraphIso
    (source (graph core3860) (root 8) 1 4) DegreeTwoThreeSpectrum4324.graph sourceMap3860=true := by decide +kernel
theorem fusedMap3860_checked : acceptsGraphIso
    (fused (graph core3860) (root 8) 1 4) DegreeTwoThreeSpectrum3932.graph fusedMap3860=true := by decide +kernel
theorem certified3860 : Certified (graph core3860) (root 8) 1 4 :=
  of_native_maps core3860 DegreeTwoThreeSpectrum4324.graph DegreeTwoThreeSpectrum3932.graph
    sourceMap3860 fusedMap3860 sourceMap3860_checked fusedMap3860_checked
    DegreeTwoThreeFiniteComparisons.comparison3860
#print axioms sourceMap3860_checked
#print axioms fusedMap3860_checked
#print axioms certified3860
def sourceMap3860swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3860swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3860swap_checked : acceptsGraphIso
    (source (graph core3860) (root 8) 4 1) DegreeTwoThreeSpectrum4324.graph sourceMap3860swap=true := by decide +kernel
theorem fusedMap3860swap_checked : acceptsGraphIso
    (fused (graph core3860) (root 8) 4 1) DegreeTwoThreeSpectrum3932.graph fusedMap3860swap=true := by decide +kernel
theorem certified3860swap : Certified (graph core3860) (root 8) 4 1 :=
  of_native_maps core3860 DegreeTwoThreeSpectrum4324.graph DegreeTwoThreeSpectrum3932.graph
    sourceMap3860swap fusedMap3860swap sourceMap3860swap_checked fusedMap3860swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3860
#print axioms sourceMap3860swap_checked
#print axioms fusedMap3860swap_checked
#print axioms certified3860swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
