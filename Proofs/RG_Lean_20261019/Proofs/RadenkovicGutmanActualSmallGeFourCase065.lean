/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core065 : Family 7 := level7.get ⟨80,by decide⟩
def sourceMap065 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![4,0,1,2,3,7,8,9,10,5,6] (sourceLabel 7 0 1 v)
def fusedMap065 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7] (fusedLabel 7 0 1 v)
theorem sourceMap065_checked : acceptsGraphIso
    (source (graph core065) (root 7) 0 1) SmallGeFourSpectrum052.graph
      sourceMap065=true := by decide +kernel
theorem fusedMap065_checked : acceptsGraphIso
    (fused (graph core065) (root 7) 0 1) SmallGeFourSpectrum054.graph
      fusedMap065=true := by decide +kernel
theorem certified065 : Certified (graph core065) (root 7) 0 1 :=
  of_native_maps core065 SmallGeFourSpectrum052.graph SmallGeFourSpectrum054.graph
    sourceMap065 fusedMap065 sourceMap065_checked fusedMap065_checked
    SmallGeFourComparisons.comparison065
#print axioms sourceMap065_checked
#print axioms fusedMap065_checked
#print axioms certified065
def sourceMap065swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![4,0,1,2,3,7,8,9,5,6,10] (sourceLabel 7 1 0 v)
def fusedMap065swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7] (fusedLabel 7 1 0 v)
theorem sourceMap065swap_checked : acceptsGraphIso
    (source (graph core065) (root 7) 1 0) SmallGeFourSpectrum052.graph
      sourceMap065swap=true := by decide +kernel
theorem fusedMap065swap_checked : acceptsGraphIso
    (fused (graph core065) (root 7) 1 0) SmallGeFourSpectrum054.graph
      fusedMap065swap=true := by decide +kernel
theorem certified065swap : Certified (graph core065) (root 7) 1 0 :=
  of_native_maps core065 SmallGeFourSpectrum052.graph SmallGeFourSpectrum054.graph
    sourceMap065swap fusedMap065swap sourceMap065swap_checked fusedMap065swap_checked
    SmallGeFourComparisons.comparison065
#print axioms sourceMap065swap_checked
#print axioms fusedMap065swap_checked
#print axioms certified065swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
