/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2570 : Family 10 := level10.get ⟨445,by decide⟩
def sourceMap2570 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2570 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2570_checked : acceptsGraphIso
    (source (graph core2570) (root 10) 0 4) DegreeTwoThreeSpectrum5864.graph sourceMap2570=true := by decide +kernel
theorem fusedMap2570_checked : acceptsGraphIso
    (fused (graph core2570) (root 10) 0 4) DegreeTwoThreeSpectrum5866.graph fusedMap2570=true := by decide +kernel
theorem certified2570 : Certified (graph core2570) (root 10) 0 4 :=
  of_native_maps core2570 DegreeTwoThreeSpectrum5864.graph DegreeTwoThreeSpectrum5866.graph
    sourceMap2570 fusedMap2570 sourceMap2570_checked fusedMap2570_checked
    DegreeTwoThreeFiniteComparisons.comparison2570
#print axioms sourceMap2570_checked
#print axioms fusedMap2570_checked
#print axioms certified2570
def sourceMap2570swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2570swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2570swap_checked : acceptsGraphIso
    (source (graph core2570) (root 10) 4 0) DegreeTwoThreeSpectrum5864.graph sourceMap2570swap=true := by decide +kernel
theorem fusedMap2570swap_checked : acceptsGraphIso
    (fused (graph core2570) (root 10) 4 0) DegreeTwoThreeSpectrum5866.graph fusedMap2570swap=true := by decide +kernel
theorem certified2570swap : Certified (graph core2570) (root 10) 4 0 :=
  of_native_maps core2570 DegreeTwoThreeSpectrum5864.graph DegreeTwoThreeSpectrum5866.graph
    sourceMap2570swap fusedMap2570swap sourceMap2570swap_checked fusedMap2570swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2570
#print axioms sourceMap2570swap_checked
#print axioms fusedMap2570swap_checked
#print axioms certified2570swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
