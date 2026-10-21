/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core130 : Family 8 := level8.get ⟨247,by decide⟩
def sourceMap130 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap130 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,3,4,5,1,2] (fusedLabel 8 0 0 v)
theorem sourceMap130_checked : acceptsGraphIso
    (source (graph core130) (root 8) 0 0) SmallGeFourSpectrum079.graph
      sourceMap130=true := by decide +kernel
theorem fusedMap130_checked : acceptsGraphIso
    (fused (graph core130) (root 8) 0 0) SmallGeFourSpectrum063.graph
      fusedMap130=true := by decide +kernel
theorem certified130 : Certified (graph core130) (root 8) 0 0 :=
  of_native_maps core130 SmallGeFourSpectrum079.graph SmallGeFourSpectrum063.graph
    sourceMap130 fusedMap130 sourceMap130_checked fusedMap130_checked
    SmallGeFourComparisons.comparison130
#print axioms sourceMap130_checked
#print axioms fusedMap130_checked
#print axioms certified130
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
