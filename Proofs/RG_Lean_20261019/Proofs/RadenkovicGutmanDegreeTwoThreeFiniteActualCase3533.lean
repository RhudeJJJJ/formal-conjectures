/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3533 : Family 7 := level7.get ⟨90,by decide⟩
def sourceMap3533 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3533 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3533_checked : acceptsGraphIso
    (source (graph core3533) (root 7) 0 6) DegreeTwoThreeSpectrum4484.graph sourceMap3533=true := by decide +kernel
theorem fusedMap3533_checked : acceptsGraphIso
    (fused (graph core3533) (root 7) 0 6) DegreeTwoThreeSpectrum4018.graph fusedMap3533=true := by decide +kernel
theorem certified3533 : Certified (graph core3533) (root 7) 0 6 :=
  of_native_maps core3533 DegreeTwoThreeSpectrum4484.graph DegreeTwoThreeSpectrum4018.graph
    sourceMap3533 fusedMap3533 sourceMap3533_checked fusedMap3533_checked
    DegreeTwoThreeFiniteComparisons.comparison3533
#print axioms sourceMap3533_checked
#print axioms fusedMap3533_checked
#print axioms certified3533
def sourceMap3533swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3533swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3533swap_checked : acceptsGraphIso
    (source (graph core3533) (root 7) 6 0) DegreeTwoThreeSpectrum4484.graph sourceMap3533swap=true := by decide +kernel
theorem fusedMap3533swap_checked : acceptsGraphIso
    (fused (graph core3533) (root 7) 6 0) DegreeTwoThreeSpectrum4018.graph fusedMap3533swap=true := by decide +kernel
theorem certified3533swap : Certified (graph core3533) (root 7) 6 0 :=
  of_native_maps core3533 DegreeTwoThreeSpectrum4484.graph DegreeTwoThreeSpectrum4018.graph
    sourceMap3533swap fusedMap3533swap sourceMap3533swap_checked fusedMap3533swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3533
#print axioms sourceMap3533swap_checked
#print axioms fusedMap3533swap_checked
#print axioms certified3533swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
