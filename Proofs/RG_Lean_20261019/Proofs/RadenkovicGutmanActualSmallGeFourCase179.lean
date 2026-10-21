/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core179 : Family 9 := level9.get ⟨405,by decide⟩
def sourceMap179 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,7,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap179 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,11,8,9,10,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap179_checked : acceptsGraphIso
    (source (graph core179) (root 9) 0 0) SmallGeFourSpectrum119.graph
      sourceMap179=true := by decide +kernel
theorem fusedMap179_checked : acceptsGraphIso
    (fused (graph core179) (root 9) 0 0) SmallGeFourSpectrum160.graph
      fusedMap179=true := by decide +kernel
theorem certified179 : Certified (graph core179) (root 9) 0 0 :=
  of_native_maps core179 SmallGeFourSpectrum119.graph SmallGeFourSpectrum160.graph
    sourceMap179 fusedMap179 sourceMap179_checked fusedMap179_checked
    SmallGeFourComparisons.comparison179
#print axioms sourceMap179_checked
#print axioms fusedMap179_checked
#print axioms certified179
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
