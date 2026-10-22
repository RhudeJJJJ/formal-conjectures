/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3163 : Family 8 := level8.get ⟨89,by decide⟩
def sourceMap3163 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3163 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3163_checked : acceptsGraphIso
    (source (graph core3163) (root 8) 0 5) DegreeTwoThreeSpectrum4141.graph sourceMap3163=true := by decide +kernel
theorem fusedMap3163_checked : acceptsGraphIso
    (fused (graph core3163) (root 8) 0 5) DegreeTwoThreeSpectrum4142.graph fusedMap3163=true := by decide +kernel
theorem certified3163 : Certified (graph core3163) (root 8) 0 5 :=
  of_native_maps core3163 DegreeTwoThreeSpectrum4141.graph DegreeTwoThreeSpectrum4142.graph
    sourceMap3163 fusedMap3163 sourceMap3163_checked fusedMap3163_checked
    DegreeTwoThreeFiniteComparisons.comparison3163
#print axioms sourceMap3163_checked
#print axioms fusedMap3163_checked
#print axioms certified3163
def sourceMap3163swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3163swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3163swap_checked : acceptsGraphIso
    (source (graph core3163) (root 8) 5 0) DegreeTwoThreeSpectrum4141.graph sourceMap3163swap=true := by decide +kernel
theorem fusedMap3163swap_checked : acceptsGraphIso
    (fused (graph core3163) (root 8) 5 0) DegreeTwoThreeSpectrum4142.graph fusedMap3163swap=true := by decide +kernel
theorem certified3163swap : Certified (graph core3163) (root 8) 5 0 :=
  of_native_maps core3163 DegreeTwoThreeSpectrum4141.graph DegreeTwoThreeSpectrum4142.graph
    sourceMap3163swap fusedMap3163swap sourceMap3163swap_checked fusedMap3163swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3163
#print axioms sourceMap3163swap_checked
#print axioms fusedMap3163swap_checked
#print axioms certified3163swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
