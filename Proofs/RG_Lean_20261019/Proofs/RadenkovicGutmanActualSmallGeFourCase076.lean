/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core076 : Family 7 := level7.get ⟨99,by decide⟩
def sourceMap076 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,8,9,2,3,4,5,6,7] (sourceLabel 7 0 0 v)
def fusedMap076 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,7,8,9,3,4,5,6,1,2] (fusedLabel 7 0 0 v)
theorem sourceMap076_checked : acceptsGraphIso
    (source (graph core076) (root 7) 0 0) SmallGeFourSpectrum026.graph
      sourceMap076=true := by decide +kernel
theorem fusedMap076_checked : acceptsGraphIso
    (fused (graph core076) (root 7) 0 0) SmallGeFourSpectrum020.graph
      fusedMap076=true := by decide +kernel
theorem certified076 : Certified (graph core076) (root 7) 0 0 :=
  of_native_maps core076 SmallGeFourSpectrum026.graph SmallGeFourSpectrum020.graph
    sourceMap076 fusedMap076 sourceMap076_checked fusedMap076_checked
    SmallGeFourComparisons.comparison076
#print axioms sourceMap076_checked
#print axioms fusedMap076_checked
#print axioms certified076
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
