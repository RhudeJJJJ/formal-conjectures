/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core203 : Family 9 := level9.get ⟨615,by decide⟩
def sourceMap203 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap203 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap203_checked : acceptsGraphIso
    (source (graph core203) (root 9) 0 0) SmallGeFourSpectrum205.graph
      sourceMap203=true := by decide +kernel
theorem fusedMap203_checked : acceptsGraphIso
    (fused (graph core203) (root 9) 0 0) SmallGeFourSpectrum152.graph
      fusedMap203=true := by decide +kernel
theorem certified203 : Certified (graph core203) (root 9) 0 0 :=
  of_native_maps core203 SmallGeFourSpectrum205.graph SmallGeFourSpectrum152.graph
    sourceMap203 fusedMap203 sourceMap203_checked fusedMap203_checked
    SmallGeFourComparisons.comparison203
#print axioms sourceMap203_checked
#print axioms fusedMap203_checked
#print axioms certified203
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
