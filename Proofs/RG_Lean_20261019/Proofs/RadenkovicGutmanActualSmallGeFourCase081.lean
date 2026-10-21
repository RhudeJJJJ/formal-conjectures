/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core081 : Family 7 := level7.get ⟨106,by decide⟩
def sourceMap081 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,7,8,9,10,5,6] (sourceLabel 7 0 1 v)
def fusedMap081 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap081_checked : acceptsGraphIso
    (source (graph core081) (root 7) 0 1) SmallGeFourSpectrum082.graph
      sourceMap081=true := by decide +kernel
theorem fusedMap081_checked : acceptsGraphIso
    (fused (graph core081) (root 7) 0 1) SmallGeFourSpectrum045.graph
      fusedMap081=true := by decide +kernel
theorem certified081 : Certified (graph core081) (root 7) 0 1 :=
  of_native_maps core081 SmallGeFourSpectrum082.graph SmallGeFourSpectrum045.graph
    sourceMap081 fusedMap081 sourceMap081_checked fusedMap081_checked
    SmallGeFourComparisons.comparison081
#print axioms sourceMap081_checked
#print axioms fusedMap081_checked
#print axioms certified081
def sourceMap081swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,7,8,9,5,6,10] (sourceLabel 7 1 0 v)
def fusedMap081swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap081swap_checked : acceptsGraphIso
    (source (graph core081) (root 7) 1 0) SmallGeFourSpectrum082.graph
      sourceMap081swap=true := by decide +kernel
theorem fusedMap081swap_checked : acceptsGraphIso
    (fused (graph core081) (root 7) 1 0) SmallGeFourSpectrum045.graph
      fusedMap081swap=true := by decide +kernel
theorem certified081swap : Certified (graph core081) (root 7) 1 0 :=
  of_native_maps core081 SmallGeFourSpectrum082.graph SmallGeFourSpectrum045.graph
    sourceMap081swap fusedMap081swap sourceMap081swap_checked fusedMap081swap_checked
    SmallGeFourComparisons.comparison081
#print axioms sourceMap081swap_checked
#print axioms fusedMap081swap_checked
#print axioms certified081swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
