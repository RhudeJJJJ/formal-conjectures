/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core175 : Family 9 := level9.get ⟨315,by decide⟩
def sourceMap175 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap175 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,6,7,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap175_checked : acceptsGraphIso
    (source (graph core175) (root 9) 0 0) SmallGeFourSpectrum100.graph
      sourceMap175=true := by decide +kernel
theorem fusedMap175_checked : acceptsGraphIso
    (fused (graph core175) (root 9) 0 0) SmallGeFourSpectrum099.graph
      fusedMap175=true := by decide +kernel
theorem certified175 : Certified (graph core175) (root 9) 0 0 :=
  of_native_maps core175 SmallGeFourSpectrum100.graph SmallGeFourSpectrum099.graph
    sourceMap175 fusedMap175 sourceMap175_checked fusedMap175_checked
    SmallGeFourComparisons.comparison175
#print axioms sourceMap175_checked
#print axioms fusedMap175_checked
#print axioms certified175
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
