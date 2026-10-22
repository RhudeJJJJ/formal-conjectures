/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2773 : Family 10 := level10.get ⟨1005,by decide⟩
def sourceMap2773 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2773 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2773_checked : acceptsGraphIso
    (source (graph core2773) (root 10) 0 4) DegreeTwoThreeSpectrum5987.graph sourceMap2773=true := by decide +kernel
theorem fusedMap2773_checked : acceptsGraphIso
    (fused (graph core2773) (root 10) 0 4) DegreeTwoThreeSpectrum5988.graph fusedMap2773=true := by decide +kernel
theorem certified2773 : Certified (graph core2773) (root 10) 0 4 :=
  of_native_maps core2773 DegreeTwoThreeSpectrum5987.graph DegreeTwoThreeSpectrum5988.graph
    sourceMap2773 fusedMap2773 sourceMap2773_checked fusedMap2773_checked
    DegreeTwoThreeFiniteComparisons.comparison2773
#print axioms sourceMap2773_checked
#print axioms fusedMap2773_checked
#print axioms certified2773
def sourceMap2773swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2773swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2773swap_checked : acceptsGraphIso
    (source (graph core2773) (root 10) 4 0) DegreeTwoThreeSpectrum5987.graph sourceMap2773swap=true := by decide +kernel
theorem fusedMap2773swap_checked : acceptsGraphIso
    (fused (graph core2773) (root 10) 4 0) DegreeTwoThreeSpectrum5988.graph fusedMap2773swap=true := by decide +kernel
theorem certified2773swap : Certified (graph core2773) (root 10) 4 0 :=
  of_native_maps core2773 DegreeTwoThreeSpectrum5987.graph DegreeTwoThreeSpectrum5988.graph
    sourceMap2773swap fusedMap2773swap sourceMap2773swap_checked fusedMap2773swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2773
#print axioms sourceMap2773swap_checked
#print axioms fusedMap2773swap_checked
#print axioms certified2773swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
