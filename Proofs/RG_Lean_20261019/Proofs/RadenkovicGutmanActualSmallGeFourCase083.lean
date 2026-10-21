/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core083 : Family 7 := level7.get ⟨106,by decide⟩
def sourceMap083 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,9,10,11,5,6,7,8] (sourceLabel 7 1 1 v)
def fusedMap083 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap083_checked : acceptsGraphIso
    (source (graph core083) (root 7) 1 1) SmallGeFourSpectrum220.graph
      sourceMap083=true := by decide +kernel
theorem fusedMap083_checked : acceptsGraphIso
    (fused (graph core083) (root 7) 1 1) SmallGeFourSpectrum133.graph
      fusedMap083=true := by decide +kernel
theorem certified083 : Certified (graph core083) (root 7) 1 1 :=
  of_native_maps core083 SmallGeFourSpectrum220.graph SmallGeFourSpectrum133.graph
    sourceMap083 fusedMap083 sourceMap083_checked fusedMap083_checked
    SmallGeFourComparisons.comparison083
#print axioms sourceMap083_checked
#print axioms fusedMap083_checked
#print axioms certified083
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
