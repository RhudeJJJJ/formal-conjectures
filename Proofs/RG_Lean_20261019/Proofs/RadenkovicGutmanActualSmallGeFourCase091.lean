/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core091 : Family 7 := level7.get ⟨110,by decide⟩
def sourceMap091 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,8,9,10,11,4,5,6,7] (sourceLabel 7 1 1 v)
def fusedMap091 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap091_checked : acceptsGraphIso
    (source (graph core091) (root 7) 1 1) SmallGeFourSpectrum227.graph
      sourceMap091=true := by decide +kernel
theorem fusedMap091_checked : acceptsGraphIso
    (fused (graph core091) (root 7) 1 1) SmallGeFourSpectrum149.graph
      fusedMap091=true := by decide +kernel
theorem certified091 : Certified (graph core091) (root 7) 1 1 :=
  of_native_maps core091 SmallGeFourSpectrum227.graph SmallGeFourSpectrum149.graph
    sourceMap091 fusedMap091 sourceMap091_checked fusedMap091_checked
    SmallGeFourComparisons.comparison091
#print axioms sourceMap091_checked
#print axioms fusedMap091_checked
#print axioms certified091
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
