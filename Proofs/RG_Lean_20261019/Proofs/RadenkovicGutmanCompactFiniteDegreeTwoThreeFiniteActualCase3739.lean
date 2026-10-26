/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3739 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3739 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (sourceLabel 4 0 10 v)
def fusedMap3739 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 4 0 10 v)
theorem sourceMap3739_checked : acceptsGraphIso
    (source (graph core3739) (root 4) 0 10) DegreeTwoThreeSpectrum5060.graph sourceMap3739=true := by decide +kernel
theorem fusedMap3739_checked : acceptsGraphIso
    (fused (graph core3739) (root 4) 0 10) DegreeTwoThreeSpectrum4961.graph fusedMap3739=true := by decide +kernel
theorem certified3739 : Certified (graph core3739) (root 4) 0 10 :=
  of_native_maps core3739 DegreeTwoThreeSpectrum5060.graph DegreeTwoThreeSpectrum4961.graph
    sourceMap3739 fusedMap3739 sourceMap3739_checked fusedMap3739_checked
    DegreeTwoThreeFiniteComparisons.comparison3739
#print axioms sourceMap3739_checked
#print axioms fusedMap3739_checked
#print axioms certified3739
def sourceMap3739swap : (Vertices 4 ⊕ Fin 11 ⊕ Fin 1) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,10,11,12,13,14,15,16,9] (sourceLabel 4 10 0 v)
def fusedMap3739swap : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 4 10 0 v)
theorem sourceMap3739swap_checked : acceptsGraphIso
    (source (graph core3739) (root 4) 10 0) DegreeTwoThreeSpectrum5060.graph sourceMap3739swap=true := by decide +kernel
theorem fusedMap3739swap_checked : acceptsGraphIso
    (fused (graph core3739) (root 4) 10 0) DegreeTwoThreeSpectrum4961.graph fusedMap3739swap=true := by decide +kernel
theorem certified3739swap : Certified (graph core3739) (root 4) 10 0 :=
  of_native_maps core3739 DegreeTwoThreeSpectrum5060.graph DegreeTwoThreeSpectrum4961.graph
    sourceMap3739swap fusedMap3739swap sourceMap3739swap_checked fusedMap3739swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3739
#print axioms sourceMap3739swap_checked
#print axioms fusedMap3739swap_checked
#print axioms certified3739swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
