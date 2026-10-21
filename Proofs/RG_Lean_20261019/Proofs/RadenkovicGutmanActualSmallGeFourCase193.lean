/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core193 : Family 9 := level9.get ⟨539,by decide⟩
def sourceMap193 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap193 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,5,8,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap193_checked : acceptsGraphIso
    (source (graph core193) (root 9) 0 0) SmallGeFourSpectrum169.graph
      sourceMap193=true := by decide +kernel
theorem fusedMap193_checked : acceptsGraphIso
    (fused (graph core193) (root 9) 0 0) SmallGeFourSpectrum166.graph
      fusedMap193=true := by decide +kernel
theorem certified193 : Certified (graph core193) (root 9) 0 0 :=
  of_native_maps core193 SmallGeFourSpectrum169.graph SmallGeFourSpectrum166.graph
    sourceMap193 fusedMap193 sourceMap193_checked fusedMap193_checked
    SmallGeFourComparisons.comparison193
#print axioms sourceMap193_checked
#print axioms fusedMap193_checked
#print axioms certified193
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
