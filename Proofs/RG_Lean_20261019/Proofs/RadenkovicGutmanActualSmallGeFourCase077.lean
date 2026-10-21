/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core077 : Family 7 := level7.get ⟨99,by decide⟩
def sourceMap077 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,8,9,10,3,4,5,6,7,1,2] (sourceLabel 7 0 1 v)
def fusedMap077 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6] (fusedLabel 7 0 1 v)
theorem sourceMap077_checked : acceptsGraphIso
    (source (graph core077) (root 7) 0 1) SmallGeFourSpectrum060.graph
      sourceMap077=true := by decide +kernel
theorem fusedMap077_checked : acceptsGraphIso
    (fused (graph core077) (root 7) 0 1) SmallGeFourSpectrum068.graph
      fusedMap077=true := by decide +kernel
theorem certified077 : Certified (graph core077) (root 7) 0 1 :=
  of_native_maps core077 SmallGeFourSpectrum060.graph SmallGeFourSpectrum068.graph
    sourceMap077 fusedMap077 sourceMap077_checked fusedMap077_checked
    SmallGeFourComparisons.comparison077
#print axioms sourceMap077_checked
#print axioms fusedMap077_checked
#print axioms certified077
def sourceMap077swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,8,9,10,3,4,5,6,1,2,7] (sourceLabel 7 1 0 v)
def fusedMap077swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6] (fusedLabel 7 1 0 v)
theorem sourceMap077swap_checked : acceptsGraphIso
    (source (graph core077) (root 7) 1 0) SmallGeFourSpectrum060.graph
      sourceMap077swap=true := by decide +kernel
theorem fusedMap077swap_checked : acceptsGraphIso
    (fused (graph core077) (root 7) 1 0) SmallGeFourSpectrum068.graph
      fusedMap077swap=true := by decide +kernel
theorem certified077swap : Certified (graph core077) (root 7) 1 0 :=
  of_native_maps core077 SmallGeFourSpectrum060.graph SmallGeFourSpectrum068.graph
    sourceMap077swap fusedMap077swap sourceMap077swap_checked fusedMap077swap_checked
    SmallGeFourComparisons.comparison077
#print axioms sourceMap077swap_checked
#print axioms fusedMap077swap_checked
#print axioms certified077swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
