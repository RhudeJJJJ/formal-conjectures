/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core084 : Family 7 := level7.get ⟨109,by decide⟩
def sourceMap084 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap084 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap084_checked : acceptsGraphIso
    (source (graph core084) (root 7) 0 0) SmallGeFourSpectrum032.graph
      sourceMap084=true := by decide +kernel
theorem fusedMap084_checked : acceptsGraphIso
    (fused (graph core084) (root 7) 0 0) SmallGeFourSpectrum031.graph
      fusedMap084=true := by decide +kernel
theorem certified084 : Certified (graph core084) (root 7) 0 0 :=
  of_native_maps core084 SmallGeFourSpectrum032.graph SmallGeFourSpectrum031.graph
    sourceMap084 fusedMap084 sourceMap084_checked fusedMap084_checked
    SmallGeFourComparisons.comparison084
#print axioms sourceMap084_checked
#print axioms fusedMap084_checked
#print axioms certified084
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
