/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3880 : Family 8 := level8.get ⟨169,by decide⟩
def sourceMap3880 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3880 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3880_checked : acceptsGraphIso
    (source (graph core3880) (root 8) 1 4) DegreeTwoThreeSpectrum4589.graph sourceMap3880=true := by decide +kernel
theorem fusedMap3880_checked : acceptsGraphIso
    (fused (graph core3880) (root 8) 1 4) DegreeTwoThreeSpectrum4072.graph fusedMap3880=true := by decide +kernel
theorem certified3880 : Certified (graph core3880) (root 8) 1 4 :=
  of_native_maps core3880 DegreeTwoThreeSpectrum4589.graph DegreeTwoThreeSpectrum4072.graph
    sourceMap3880 fusedMap3880 sourceMap3880_checked fusedMap3880_checked
    DegreeTwoThreeFiniteComparisons.comparison3880
#print axioms sourceMap3880_checked
#print axioms fusedMap3880_checked
#print axioms certified3880
def sourceMap3880swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3880swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3880swap_checked : acceptsGraphIso
    (source (graph core3880) (root 8) 4 1) DegreeTwoThreeSpectrum4589.graph sourceMap3880swap=true := by decide +kernel
theorem fusedMap3880swap_checked : acceptsGraphIso
    (fused (graph core3880) (root 8) 4 1) DegreeTwoThreeSpectrum4072.graph fusedMap3880swap=true := by decide +kernel
theorem certified3880swap : Certified (graph core3880) (root 8) 4 1 :=
  of_native_maps core3880 DegreeTwoThreeSpectrum4589.graph DegreeTwoThreeSpectrum4072.graph
    sourceMap3880swap fusedMap3880swap sourceMap3880swap_checked fusedMap3880swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3880
#print axioms sourceMap3880swap_checked
#print axioms fusedMap3880swap_checked
#print axioms certified3880swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
