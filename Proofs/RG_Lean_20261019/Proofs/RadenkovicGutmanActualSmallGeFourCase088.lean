/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core088 : Family 7 := level7.get ⟨110,by decide⟩
def sourceMap088 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (sourceLabel 7 0 0 v)
def fusedMap088 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,6,7,8,9,4,5] (fusedLabel 7 0 0 v)
theorem sourceMap088_checked : acceptsGraphIso
    (source (graph core088) (root 7) 0 0) SmallGeFourSpectrum025.graph
      sourceMap088=true := by decide +kernel
theorem fusedMap088_checked : acceptsGraphIso
    (fused (graph core088) (root 7) 0 0) SmallGeFourSpectrum032.graph
      fusedMap088=true := by decide +kernel
theorem certified088 : Certified (graph core088) (root 7) 0 0 :=
  of_native_maps core088 SmallGeFourSpectrum025.graph SmallGeFourSpectrum032.graph
    sourceMap088 fusedMap088 sourceMap088_checked fusedMap088_checked
    SmallGeFourComparisons.comparison088
#print axioms sourceMap088_checked
#print axioms fusedMap088_checked
#print axioms certified088
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
