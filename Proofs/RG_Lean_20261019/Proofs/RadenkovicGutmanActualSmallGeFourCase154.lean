/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core154 : Family 8 := level8.get ⟨278,by decide⟩
def sourceMap154 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap154 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap154_checked : acceptsGraphIso
    (source (graph core154) (root 8) 0 0) SmallGeFourSpectrum086.graph
      sourceMap154=true := by decide +kernel
theorem fusedMap154_checked : acceptsGraphIso
    (fused (graph core154) (root 8) 0 0) SmallGeFourSpectrum085.graph
      fusedMap154=true := by decide +kernel
theorem certified154 : Certified (graph core154) (root 8) 0 0 :=
  of_native_maps core154 SmallGeFourSpectrum086.graph SmallGeFourSpectrum085.graph
    sourceMap154 fusedMap154 sourceMap154_checked fusedMap154_checked
    SmallGeFourComparisons.comparison154
#print axioms sourceMap154_checked
#print axioms fusedMap154_checked
#print axioms certified154
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
