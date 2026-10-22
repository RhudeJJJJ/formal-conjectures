/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3721 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap3721 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3721 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3721_checked : acceptsGraphIso
    (source (graph core3721) (root 6) 0 8) DegreeTwoThreeSpectrum5661.graph sourceMap3721=true := by decide +kernel
theorem fusedMap3721_checked : acceptsGraphIso
    (fused (graph core3721) (root 6) 0 8) DegreeTwoThreeSpectrum5048.graph fusedMap3721=true := by decide +kernel
theorem certified3721 : Certified (graph core3721) (root 6) 0 8 :=
  of_native_maps core3721 DegreeTwoThreeSpectrum5661.graph DegreeTwoThreeSpectrum5048.graph
    sourceMap3721 fusedMap3721 sourceMap3721_checked fusedMap3721_checked
    DegreeTwoThreeFiniteComparisons.comparison3721
#print axioms sourceMap3721_checked
#print axioms fusedMap3721_checked
#print axioms certified3721
def sourceMap3721swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,11,12,13,14,15,16,10] (sourceLabel 6 8 0 v)
def fusedMap3721swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3721swap_checked : acceptsGraphIso
    (source (graph core3721) (root 6) 8 0) DegreeTwoThreeSpectrum5661.graph sourceMap3721swap=true := by decide +kernel
theorem fusedMap3721swap_checked : acceptsGraphIso
    (fused (graph core3721) (root 6) 8 0) DegreeTwoThreeSpectrum5048.graph fusedMap3721swap=true := by decide +kernel
theorem certified3721swap : Certified (graph core3721) (root 6) 8 0 :=
  of_native_maps core3721 DegreeTwoThreeSpectrum5661.graph DegreeTwoThreeSpectrum5048.graph
    sourceMap3721swap fusedMap3721swap sourceMap3721swap_checked fusedMap3721swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3721
#print axioms sourceMap3721swap_checked
#print axioms fusedMap3721swap_checked
#print axioms certified3721swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
