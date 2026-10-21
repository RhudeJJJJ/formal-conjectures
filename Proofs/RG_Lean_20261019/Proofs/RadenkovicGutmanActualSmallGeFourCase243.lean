/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core243 : Family 9 := level9.get ⟨715,by decide⟩
def sourceMap243 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap243 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap243_checked : acceptsGraphIso
    (source (graph core243) (root 9) 0 0) SmallGeFourSpectrum231.graph
      sourceMap243=true := by decide +kernel
theorem fusedMap243_checked : acceptsGraphIso
    (fused (graph core243) (root 9) 0 0) SmallGeFourSpectrum230.graph
      fusedMap243=true := by decide +kernel
theorem certified243 : Certified (graph core243) (root 9) 0 0 :=
  of_native_maps core243 SmallGeFourSpectrum231.graph SmallGeFourSpectrum230.graph
    sourceMap243 fusedMap243 sourceMap243_checked fusedMap243_checked
    SmallGeFourComparisons.comparison243
#print axioms sourceMap243_checked
#print axioms fusedMap243_checked
#print axioms certified243
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
