/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core236 : Family 9 := level9.get ⟨708,by decide⟩
def sourceMap236 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap236 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap236_checked : acceptsGraphIso
    (source (graph core236) (root 9) 0 0) SmallGeFourSpectrum223.graph
      sourceMap236=true := by decide +kernel
theorem fusedMap236_checked : acceptsGraphIso
    (fused (graph core236) (root 9) 0 0) SmallGeFourSpectrum222.graph
      fusedMap236=true := by decide +kernel
theorem certified236 : Certified (graph core236) (root 9) 0 0 :=
  of_native_maps core236 SmallGeFourSpectrum223.graph SmallGeFourSpectrum222.graph
    sourceMap236 fusedMap236 sourceMap236_checked fusedMap236_checked
    SmallGeFourComparisons.comparison236
#print axioms sourceMap236_checked
#print axioms fusedMap236_checked
#print axioms certified236
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
