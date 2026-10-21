/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core245 : Family 9 := level9.get ⟨717,by decide⟩
def sourceMap245 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,10,11,1,2,3,4,5,6,7,8,9] (sourceLabel 9 0 0 v)
def fusedMap245 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,5,6,7,8,9,10,11,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap245_checked : acceptsGraphIso
    (source (graph core245) (root 9) 0 0) SmallGeFourSpectrum197.graph
      sourceMap245=true := by decide +kernel
theorem fusedMap245_checked : acceptsGraphIso
    (fused (graph core245) (root 9) 0 0) SmallGeFourSpectrum232.graph
      fusedMap245=true := by decide +kernel
theorem certified245 : Certified (graph core245) (root 9) 0 0 :=
  of_native_maps core245 SmallGeFourSpectrum197.graph SmallGeFourSpectrum232.graph
    sourceMap245 fusedMap245 sourceMap245_checked fusedMap245_checked
    SmallGeFourComparisons.comparison245
#print axioms sourceMap245_checked
#print axioms fusedMap245_checked
#print axioms certified245
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
