/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core211 : Family 9 := level9.get ⟨648,by decide⟩
def sourceMap211 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap211 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap211_checked : acceptsGraphIso
    (source (graph core211) (root 9) 0 0) SmallGeFourSpectrum206.graph
      sourceMap211=true := by decide +kernel
theorem fusedMap211_checked : acceptsGraphIso
    (fused (graph core211) (root 9) 0 0) SmallGeFourSpectrum175.graph
      fusedMap211=true := by decide +kernel
theorem certified211 : Certified (graph core211) (root 9) 0 0 :=
  of_native_maps core211 SmallGeFourSpectrum206.graph SmallGeFourSpectrum175.graph
    sourceMap211 fusedMap211 sourceMap211_checked fusedMap211_checked
    SmallGeFourComparisons.comparison211
#print axioms sourceMap211_checked
#print axioms fusedMap211_checked
#print axioms certified211
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
