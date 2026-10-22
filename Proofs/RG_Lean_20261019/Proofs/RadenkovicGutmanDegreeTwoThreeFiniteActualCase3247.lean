/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3247 : Family 9 := level9.get ⟨63,by decide⟩
def sourceMap3247 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 9 0 5 v)
def fusedMap3247 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3247_checked : acceptsGraphIso
    (source (graph core3247) (root 9) 0 5) DegreeTwoThreeSpectrum5395.graph sourceMap3247=true := by decide +kernel
theorem fusedMap3247_checked : acceptsGraphIso
    (fused (graph core3247) (root 9) 0 5) DegreeTwoThreeSpectrum4991.graph fusedMap3247=true := by decide +kernel
theorem certified3247 : Certified (graph core3247) (root 9) 0 5 :=
  of_native_maps core3247 DegreeTwoThreeSpectrum5395.graph DegreeTwoThreeSpectrum4991.graph
    sourceMap3247 fusedMap3247 sourceMap3247_checked fusedMap3247_checked
    DegreeTwoThreeFiniteComparisons.comparison3247
#print axioms sourceMap3247_checked
#print axioms fusedMap3247_checked
#print axioms certified3247
def sourceMap3247swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14,16] (sourceLabel 9 5 0 v)
def fusedMap3247swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3247swap_checked : acceptsGraphIso
    (source (graph core3247) (root 9) 5 0) DegreeTwoThreeSpectrum5395.graph sourceMap3247swap=true := by decide +kernel
theorem fusedMap3247swap_checked : acceptsGraphIso
    (fused (graph core3247) (root 9) 5 0) DegreeTwoThreeSpectrum4991.graph fusedMap3247swap=true := by decide +kernel
theorem certified3247swap : Certified (graph core3247) (root 9) 5 0 :=
  of_native_maps core3247 DegreeTwoThreeSpectrum5395.graph DegreeTwoThreeSpectrum4991.graph
    sourceMap3247swap fusedMap3247swap sourceMap3247swap_checked fusedMap3247swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3247
#print axioms sourceMap3247swap_checked
#print axioms fusedMap3247swap_checked
#print axioms certified3247swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
