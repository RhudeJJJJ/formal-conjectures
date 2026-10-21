/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core216 : Family 9 := level9.get ⟨670,by decide⟩
def sourceMap216 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap216 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,6,7,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap216_checked : acceptsGraphIso
    (source (graph core216) (root 9) 0 0) SmallGeFourSpectrum148.graph
      sourceMap216=true := by decide +kernel
theorem fusedMap216_checked : acceptsGraphIso
    (fused (graph core216) (root 9) 0 0) SmallGeFourSpectrum143.graph
      fusedMap216=true := by decide +kernel
theorem certified216 : Certified (graph core216) (root 9) 0 0 :=
  of_native_maps core216 SmallGeFourSpectrum148.graph SmallGeFourSpectrum143.graph
    sourceMap216 fusedMap216 sourceMap216_checked fusedMap216_checked
    SmallGeFourComparisons.comparison216
#print axioms sourceMap216_checked
#print axioms fusedMap216_checked
#print axioms certified216
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
