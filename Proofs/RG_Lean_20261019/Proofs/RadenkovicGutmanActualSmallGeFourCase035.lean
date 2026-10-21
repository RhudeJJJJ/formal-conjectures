/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core035 : Family 6 := level6.get ⟨36,by decide⟩
def sourceMap035 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,9,10,11,7,8,4,5,6] (sourceLabel 6 1 2 v)
def fusedMap035 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap035_checked : acceptsGraphIso
    (source (graph core035) (root 6) 1 2) SmallGeFourSpectrum195.graph
      sourceMap035=true := by decide +kernel
theorem fusedMap035_checked : acceptsGraphIso
    (fused (graph core035) (root 6) 1 2) SmallGeFourSpectrum110.graph
      fusedMap035=true := by decide +kernel
theorem certified035 : Certified (graph core035) (root 6) 1 2 :=
  of_native_maps core035 SmallGeFourSpectrum195.graph SmallGeFourSpectrum110.graph
    sourceMap035 fusedMap035 sourceMap035_checked fusedMap035_checked
    SmallGeFourComparisons.comparison035
#print axioms sourceMap035_checked
#print axioms fusedMap035_checked
#print axioms certified035
def sourceMap035swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,9,10,11,4,5,6,7,8] (sourceLabel 6 2 1 v)
def fusedMap035swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap035swap_checked : acceptsGraphIso
    (source (graph core035) (root 6) 2 1) SmallGeFourSpectrum195.graph
      sourceMap035swap=true := by decide +kernel
theorem fusedMap035swap_checked : acceptsGraphIso
    (fused (graph core035) (root 6) 2 1) SmallGeFourSpectrum110.graph
      fusedMap035swap=true := by decide +kernel
theorem certified035swap : Certified (graph core035) (root 6) 2 1 :=
  of_native_maps core035 SmallGeFourSpectrum195.graph SmallGeFourSpectrum110.graph
    sourceMap035swap fusedMap035swap sourceMap035swap_checked fusedMap035swap_checked
    SmallGeFourComparisons.comparison035
#print axioms sourceMap035swap_checked
#print axioms fusedMap035swap_checked
#print axioms certified035swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
