/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3516 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap3516 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3516 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3516_checked : acceptsGraphIso
    (source (graph core3516) (root 7) 0 6) DegreeTwoThreeSpectrum4073.graph sourceMap3516=true := by decide +kernel
theorem fusedMap3516_checked : acceptsGraphIso
    (fused (graph core3516) (root 7) 0 6) DegreeTwoThreeSpectrum4075.graph fusedMap3516=true := by decide +kernel
theorem certified3516 : Certified (graph core3516) (root 7) 0 6 :=
  of_native_maps core3516 DegreeTwoThreeSpectrum4073.graph DegreeTwoThreeSpectrum4075.graph
    sourceMap3516 fusedMap3516 sourceMap3516_checked fusedMap3516_checked
    DegreeTwoThreeFiniteComparisons.comparison3516
#print axioms sourceMap3516_checked
#print axioms fusedMap3516_checked
#print axioms certified3516
def sourceMap3516swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3516swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3516swap_checked : acceptsGraphIso
    (source (graph core3516) (root 7) 6 0) DegreeTwoThreeSpectrum4073.graph sourceMap3516swap=true := by decide +kernel
theorem fusedMap3516swap_checked : acceptsGraphIso
    (fused (graph core3516) (root 7) 6 0) DegreeTwoThreeSpectrum4075.graph fusedMap3516swap=true := by decide +kernel
theorem certified3516swap : Certified (graph core3516) (root 7) 6 0 :=
  of_native_maps core3516 DegreeTwoThreeSpectrum4073.graph DegreeTwoThreeSpectrum4075.graph
    sourceMap3516swap fusedMap3516swap sourceMap3516swap_checked fusedMap3516swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3516
#print axioms sourceMap3516swap_checked
#print axioms fusedMap3516swap_checked
#print axioms certified3516swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
