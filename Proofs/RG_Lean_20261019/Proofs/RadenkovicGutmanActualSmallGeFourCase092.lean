/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core092 : Family 7 := level7.get ⟨111,by decide⟩
def sourceMap092 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap092 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap092_checked : acceptsGraphIso
    (source (graph core092) (root 7) 0 0) SmallGeFourSpectrum034.graph
      sourceMap092=true := by decide +kernel
theorem fusedMap092_checked : acceptsGraphIso
    (fused (graph core092) (root 7) 0 0) SmallGeFourSpectrum033.graph
      fusedMap092=true := by decide +kernel
theorem certified092 : Certified (graph core092) (root 7) 0 0 :=
  of_native_maps core092 SmallGeFourSpectrum034.graph SmallGeFourSpectrum033.graph
    sourceMap092 fusedMap092 sourceMap092_checked fusedMap092_checked
    SmallGeFourComparisons.comparison092
#print axioms sourceMap092_checked
#print axioms fusedMap092_checked
#print axioms certified092
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
