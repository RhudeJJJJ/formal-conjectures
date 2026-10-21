/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core185 : Family 9 := level9.get ⟨484,by decide⟩
def sourceMap185 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap185 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,6,7,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap185_checked : acceptsGraphIso
    (source (graph core185) (root 9) 0 0) SmallGeFourSpectrum182.graph
      sourceMap185=true := by decide +kernel
theorem fusedMap185_checked : acceptsGraphIso
    (fused (graph core185) (root 9) 0 0) SmallGeFourSpectrum172.graph
      fusedMap185=true := by decide +kernel
theorem certified185 : Certified (graph core185) (root 9) 0 0 :=
  of_native_maps core185 SmallGeFourSpectrum182.graph SmallGeFourSpectrum172.graph
    sourceMap185 fusedMap185 sourceMap185_checked fusedMap185_checked
    SmallGeFourComparisons.comparison185
#print axioms sourceMap185_checked
#print axioms fusedMap185_checked
#print axioms certified185
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
