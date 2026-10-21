/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core150 : Family 8 := level8.get ⟨275,by decide⟩
def sourceMap150 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap150 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,7,8,9,10,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap150_checked : acceptsGraphIso
    (source (graph core150) (root 8) 0 0) SmallGeFourSpectrum072.graph
      sourceMap150=true := by decide +kernel
theorem fusedMap150_checked : acceptsGraphIso
    (fused (graph core150) (root 8) 0 0) SmallGeFourSpectrum082.graph
      fusedMap150=true := by decide +kernel
theorem certified150 : Certified (graph core150) (root 8) 0 0 :=
  of_native_maps core150 SmallGeFourSpectrum072.graph SmallGeFourSpectrum082.graph
    sourceMap150 fusedMap150 sourceMap150_checked fusedMap150_checked
    SmallGeFourComparisons.comparison150
#print axioms sourceMap150_checked
#print axioms fusedMap150_checked
#print axioms certified150
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
