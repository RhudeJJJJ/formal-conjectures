/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3741 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3741 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (sourceLabel 4 0 10 v)
def fusedMap3741 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 0 10 v)
theorem sourceMap3741_checked : acceptsGraphIso
    (source (graph core3741) (root 4) 0 10) DegreeTwoThreeSpectrum5008.graph sourceMap3741=true := by decide +kernel
theorem fusedMap3741_checked : acceptsGraphIso
    (fused (graph core3741) (root 4) 0 10) DegreeTwoThreeSpectrum5014.graph fusedMap3741=true := by decide +kernel
theorem certified3741 : Certified (graph core3741) (root 4) 0 10 :=
  of_native_maps core3741 DegreeTwoThreeSpectrum5008.graph DegreeTwoThreeSpectrum5014.graph
    sourceMap3741 fusedMap3741 sourceMap3741_checked fusedMap3741_checked
    DegreeTwoThreeFiniteComparisons.comparison3741
#print axioms sourceMap3741_checked
#print axioms fusedMap3741_checked
#print axioms certified3741
def sourceMap3741swap : (Vertices 4 ⊕ Fin 11 ⊕ Fin 1) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,10,11,12,13,14,15,16,9] (sourceLabel 4 10 0 v)
def fusedMap3741swap : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 10 0 v)
theorem sourceMap3741swap_checked : acceptsGraphIso
    (source (graph core3741) (root 4) 10 0) DegreeTwoThreeSpectrum5008.graph sourceMap3741swap=true := by decide +kernel
theorem fusedMap3741swap_checked : acceptsGraphIso
    (fused (graph core3741) (root 4) 10 0) DegreeTwoThreeSpectrum5014.graph fusedMap3741swap=true := by decide +kernel
theorem certified3741swap : Certified (graph core3741) (root 4) 10 0 :=
  of_native_maps core3741 DegreeTwoThreeSpectrum5008.graph DegreeTwoThreeSpectrum5014.graph
    sourceMap3741swap fusedMap3741swap sourceMap3741swap_checked fusedMap3741swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3741
#print axioms sourceMap3741swap_checked
#print axioms fusedMap3741swap_checked
#print axioms certified3741swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
