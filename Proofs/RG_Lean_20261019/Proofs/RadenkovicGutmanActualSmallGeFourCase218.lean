/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core218 : Family 9 := level9.get ⟨672,by decide⟩
def sourceMap218 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap218 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,5,6,7,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap218_checked : acceptsGraphIso
    (source (graph core218) (root 9) 0 0) SmallGeFourSpectrum179.graph
      sourceMap218=true := by decide +kernel
theorem fusedMap218_checked : acceptsGraphIso
    (fused (graph core218) (root 9) 0 0) SmallGeFourSpectrum168.graph
      fusedMap218=true := by decide +kernel
theorem certified218 : Certified (graph core218) (root 9) 0 0 :=
  of_native_maps core218 SmallGeFourSpectrum179.graph SmallGeFourSpectrum168.graph
    sourceMap218 fusedMap218 sourceMap218_checked fusedMap218_checked
    SmallGeFourComparisons.comparison218
#print axioms sourceMap218_checked
#print axioms fusedMap218_checked
#print axioms certified218
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
