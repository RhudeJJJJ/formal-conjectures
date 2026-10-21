/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core055 : Family 6 := level6.get ⟨47,by decide⟩
def sourceMap055 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 6 0 1 v)
def fusedMap055 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap055_checked : acceptsGraphIso
    (source (graph core055) (root 6) 0 1) SmallGeFourSpectrum024.graph
      sourceMap055=true := by decide +kernel
theorem fusedMap055_checked : acceptsGraphIso
    (fused (graph core055) (root 6) 0 1) SmallGeFourSpectrum026.graph
      fusedMap055=true := by decide +kernel
theorem certified055 : Certified (graph core055) (root 6) 0 1 :=
  of_native_maps core055 SmallGeFourSpectrum024.graph SmallGeFourSpectrum026.graph
    sourceMap055 fusedMap055 sourceMap055_checked fusedMap055_checked
    SmallGeFourComparisons.comparison055
#print axioms sourceMap055_checked
#print axioms fusedMap055_checked
#print axioms certified055
def sourceMap055swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,8,9,7] (sourceLabel 6 1 0 v)
def fusedMap055swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap055swap_checked : acceptsGraphIso
    (source (graph core055) (root 6) 1 0) SmallGeFourSpectrum024.graph
      sourceMap055swap=true := by decide +kernel
theorem fusedMap055swap_checked : acceptsGraphIso
    (fused (graph core055) (root 6) 1 0) SmallGeFourSpectrum026.graph
      fusedMap055swap=true := by decide +kernel
theorem certified055swap : Certified (graph core055) (root 6) 1 0 :=
  of_native_maps core055 SmallGeFourSpectrum024.graph SmallGeFourSpectrum026.graph
    sourceMap055swap fusedMap055swap sourceMap055swap_checked fusedMap055swap_checked
    SmallGeFourComparisons.comparison055
#print axioms sourceMap055swap_checked
#print axioms fusedMap055swap_checked
#print axioms certified055swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
