/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core187 : Family 9 := level9.get ⟨508,by decide⟩
def sourceMap187 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,7,8,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap187 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap187_checked : acceptsGraphIso
    (source (graph core187) (root 9) 0 0) SmallGeFourSpectrum117.graph
      sourceMap187=true := by decide +kernel
theorem fusedMap187_checked : acceptsGraphIso
    (fused (graph core187) (root 9) 0 0) SmallGeFourSpectrum187.graph
      fusedMap187=true := by decide +kernel
theorem certified187 : Certified (graph core187) (root 9) 0 0 :=
  of_native_maps core187 SmallGeFourSpectrum117.graph SmallGeFourSpectrum187.graph
    sourceMap187 fusedMap187 sourceMap187_checked fusedMap187_checked
    SmallGeFourComparisons.comparison187
#print axioms sourceMap187_checked
#print axioms fusedMap187_checked
#print axioms certified187
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
