/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core072 : Family 7 := level7.get ⟨98,by decide⟩
def sourceMap072 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap072 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,5,6,3,4] (fusedLabel 7 0 0 v)
theorem sourceMap072_checked : acceptsGraphIso
    (source (graph core072) (root 7) 0 0) SmallGeFourSpectrum020.graph
      sourceMap072=true := by decide +kernel
theorem fusedMap072_checked : acceptsGraphIso
    (fused (graph core072) (root 7) 0 0) SmallGeFourSpectrum019.graph
      fusedMap072=true := by decide +kernel
theorem certified072 : Certified (graph core072) (root 7) 0 0 :=
  of_native_maps core072 SmallGeFourSpectrum020.graph SmallGeFourSpectrum019.graph
    sourceMap072 fusedMap072 sourceMap072_checked fusedMap072_checked
    SmallGeFourComparisons.comparison072
#print axioms sourceMap072_checked
#print axioms fusedMap072_checked
#print axioms certified072
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
