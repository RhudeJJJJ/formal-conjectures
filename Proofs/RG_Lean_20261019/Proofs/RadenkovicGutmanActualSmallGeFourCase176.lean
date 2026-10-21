/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core176 : Family 9 := level9.get ⟨316,by decide⟩
def sourceMap176 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,9,10,11,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap176 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap176_checked : acceptsGraphIso
    (source (graph core176) (root 9) 0 0) SmallGeFourSpectrum116.graph
      sourceMap176=true := by decide +kernel
theorem fusedMap176_checked : acceptsGraphIso
    (fused (graph core176) (root 9) 0 0) SmallGeFourSpectrum100.graph
      fusedMap176=true := by decide +kernel
theorem certified176 : Certified (graph core176) (root 9) 0 0 :=
  of_native_maps core176 SmallGeFourSpectrum116.graph SmallGeFourSpectrum100.graph
    sourceMap176 fusedMap176 sourceMap176_checked fusedMap176_checked
    SmallGeFourComparisons.comparison176
#print axioms sourceMap176_checked
#print axioms fusedMap176_checked
#print axioms certified176
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
