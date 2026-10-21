/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core060 : Family 7 := level7.get ⟨61,by decide⟩
def sourceMap060 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap060 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,7,8,9,4,5,6,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap060_checked : acceptsGraphIso
    (source (graph core060) (root 7) 0 0) SmallGeFourSpectrum015.graph
      sourceMap060=true := by decide +kernel
theorem fusedMap060_checked : acceptsGraphIso
    (fused (graph core060) (root 7) 0 0) SmallGeFourSpectrum022.graph
      fusedMap060=true := by decide +kernel
theorem certified060 : Certified (graph core060) (root 7) 0 0 :=
  of_native_maps core060 SmallGeFourSpectrum015.graph SmallGeFourSpectrum022.graph
    sourceMap060 fusedMap060 sourceMap060_checked fusedMap060_checked
    SmallGeFourComparisons.comparison060
#print axioms sourceMap060_checked
#print axioms fusedMap060_checked
#print axioms certified060
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
