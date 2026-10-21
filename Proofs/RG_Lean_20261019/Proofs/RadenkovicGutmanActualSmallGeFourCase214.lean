/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core214 : Family 9 := level9.get ⟨663,by decide⟩
def sourceMap214 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap214 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,3,4,5,6,1,2] (fusedLabel 9 0 0 v)
theorem sourceMap214_checked : acceptsGraphIso
    (source (graph core214) (root 9) 0 0) SmallGeFourSpectrum207.graph
      sourceMap214=true := by decide +kernel
theorem fusedMap214_checked : acceptsGraphIso
    (fused (graph core214) (root 9) 0 0) SmallGeFourSpectrum181.graph
      fusedMap214=true := by decide +kernel
theorem certified214 : Certified (graph core214) (root 9) 0 0 :=
  of_native_maps core214 SmallGeFourSpectrum207.graph SmallGeFourSpectrum181.graph
    sourceMap214 fusedMap214 sourceMap214_checked fusedMap214_checked
    SmallGeFourComparisons.comparison214
#print axioms sourceMap214_checked
#print axioms fusedMap214_checked
#print axioms certified214
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
