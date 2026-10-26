/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3626 : Family 8 := level8.get ⟨244,by decide⟩
def sourceMap3626 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3626 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3626_checked : acceptsGraphIso
    (source (graph core3626) (root 8) 0 6) DegreeTwoThreeSpectrum6624.graph sourceMap3626=true := by decide +kernel
theorem fusedMap3626_checked : acceptsGraphIso
    (fused (graph core3626) (root 8) 0 6) DegreeTwoThreeSpectrum5499.graph fusedMap3626=true := by decide +kernel
theorem certified3626 : Certified (graph core3626) (root 8) 0 6 :=
  of_native_maps core3626 DegreeTwoThreeSpectrum6624.graph DegreeTwoThreeSpectrum5499.graph
    sourceMap3626 fusedMap3626 sourceMap3626_checked fusedMap3626_checked
    DegreeTwoThreeFiniteComparisons.comparison3626
#print axioms sourceMap3626_checked
#print axioms fusedMap3626_checked
#print axioms certified3626
def sourceMap3626swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3626swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3626swap_checked : acceptsGraphIso
    (source (graph core3626) (root 8) 6 0) DegreeTwoThreeSpectrum6624.graph sourceMap3626swap=true := by decide +kernel
theorem fusedMap3626swap_checked : acceptsGraphIso
    (fused (graph core3626) (root 8) 6 0) DegreeTwoThreeSpectrum5499.graph fusedMap3626swap=true := by decide +kernel
theorem certified3626swap : Certified (graph core3626) (root 8) 6 0 :=
  of_native_maps core3626 DegreeTwoThreeSpectrum6624.graph DegreeTwoThreeSpectrum5499.graph
    sourceMap3626swap fusedMap3626swap sourceMap3626swap_checked fusedMap3626swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3626
#print axioms sourceMap3626swap_checked
#print axioms fusedMap3626swap_checked
#print axioms certified3626swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
