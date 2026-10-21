/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core095 : Family 7 := level7.get ⟨111,by decide⟩
def sourceMap095 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (sourceLabel 7 1 1 v)
def fusedMap095 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap095_checked : acceptsGraphIso
    (source (graph core095) (root 7) 1 1) SmallGeFourSpectrum229.graph
      sourceMap095=true := by decide +kernel
theorem fusedMap095_checked : acceptsGraphIso
    (fused (graph core095) (root 7) 1 1) SmallGeFourSpectrum166.graph
      fusedMap095=true := by decide +kernel
theorem certified095 : Certified (graph core095) (root 7) 1 1 :=
  of_native_maps core095 SmallGeFourSpectrum229.graph SmallGeFourSpectrum166.graph
    sourceMap095 fusedMap095 sourceMap095_checked fusedMap095_checked
    SmallGeFourComparisons.comparison095
#print axioms sourceMap095_checked
#print axioms fusedMap095_checked
#print axioms certified095
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
