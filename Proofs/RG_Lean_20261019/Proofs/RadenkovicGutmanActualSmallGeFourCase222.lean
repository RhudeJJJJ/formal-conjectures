/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core222 : Family 9 := level9.get ⟨681,by decide⟩
def sourceMap222 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap222 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,7,8,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap222_checked : acceptsGraphIso
    (source (graph core222) (root 9) 0 0) SmallGeFourSpectrum132.graph
      sourceMap222=true := by decide +kernel
theorem fusedMap222_checked : acceptsGraphIso
    (fused (graph core222) (root 9) 0 0) SmallGeFourSpectrum131.graph
      fusedMap222=true := by decide +kernel
theorem certified222 : Certified (graph core222) (root 9) 0 0 :=
  of_native_maps core222 SmallGeFourSpectrum132.graph SmallGeFourSpectrum131.graph
    sourceMap222 fusedMap222 sourceMap222_checked fusedMap222_checked
    SmallGeFourComparisons.comparison222
#print axioms sourceMap222_checked
#print axioms fusedMap222_checked
#print axioms certified222
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
