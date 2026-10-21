/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core195 : Family 9 := level9.get ⟨541,by decide⟩
def sourceMap195 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap195 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,9,10,11,4,5,6,7,8,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap195_checked : acceptsGraphIso
    (source (graph core195) (root 9) 0 0) SmallGeFourSpectrum112.graph
      sourceMap195=true := by decide +kernel
theorem fusedMap195_checked : acceptsGraphIso
    (fused (graph core195) (root 9) 0 0) SmallGeFourSpectrum180.graph
      fusedMap195=true := by decide +kernel
theorem certified195 : Certified (graph core195) (root 9) 0 0 :=
  of_native_maps core195 SmallGeFourSpectrum112.graph SmallGeFourSpectrum180.graph
    sourceMap195 fusedMap195 sourceMap195_checked fusedMap195_checked
    SmallGeFourComparisons.comparison195
#print axioms sourceMap195_checked
#print axioms fusedMap195_checked
#print axioms certified195
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
