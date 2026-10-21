/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core244 : Family 9 := level9.get ⟨716,by decide⟩
def sourceMap244 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap244 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,7,8,9,10,11,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap244_checked : acceptsGraphIso
    (source (graph core244) (root 9) 0 0) SmallGeFourSpectrum232.graph
      sourceMap244=true := by decide +kernel
theorem fusedMap244_checked : acceptsGraphIso
    (fused (graph core244) (root 9) 0 0) SmallGeFourSpectrum231.graph
      fusedMap244=true := by decide +kernel
theorem certified244 : Certified (graph core244) (root 9) 0 0 :=
  of_native_maps core244 SmallGeFourSpectrum232.graph SmallGeFourSpectrum231.graph
    sourceMap244 fusedMap244 sourceMap244_checked fusedMap244_checked
    SmallGeFourComparisons.comparison244
#print axioms sourceMap244_checked
#print axioms fusedMap244_checked
#print axioms certified244
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
