/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core071 : Family 7 := level7.get ⟨93,by decide⟩
def sourceMap071 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,5,6,7,1,2,3,4] (sourceLabel 7 1 1 v)
def fusedMap071 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap071_checked : acceptsGraphIso
    (source (graph core071) (root 7) 1 1) SmallGeFourSpectrum168.graph
      sourceMap071=true := by decide +kernel
theorem fusedMap071_checked : acceptsGraphIso
    (fused (graph core071) (root 7) 1 1) SmallGeFourSpectrum105.graph
      fusedMap071=true := by decide +kernel
theorem certified071 : Certified (graph core071) (root 7) 1 1 :=
  of_native_maps core071 SmallGeFourSpectrum168.graph SmallGeFourSpectrum105.graph
    sourceMap071 fusedMap071 sourceMap071_checked fusedMap071_checked
    SmallGeFourComparisons.comparison071
#print axioms sourceMap071_checked
#print axioms fusedMap071_checked
#print axioms certified071
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
