/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core189 : Family 9 := level9.get ⟨524,by decide⟩
def sourceMap189 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap189 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,6,7,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap189_checked : acceptsGraphIso
    (source (graph core189) (root 9) 0 0) SmallGeFourSpectrum183.graph
      sourceMap189=true := by decide +kernel
theorem fusedMap189_checked : acceptsGraphIso
    (fused (graph core189) (root 9) 0 0) SmallGeFourSpectrum173.graph
      fusedMap189=true := by decide +kernel
theorem certified189 : Certified (graph core189) (root 9) 0 0 :=
  of_native_maps core189 SmallGeFourSpectrum183.graph SmallGeFourSpectrum173.graph
    sourceMap189 fusedMap189 sourceMap189_checked fusedMap189_checked
    SmallGeFourComparisons.comparison189
#print axioms sourceMap189_checked
#print axioms fusedMap189_checked
#print axioms certified189
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
