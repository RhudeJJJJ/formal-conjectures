/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core220 : Family 9 := level9.get ⟨676,by decide⟩
def sourceMap220 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap220 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap220_checked : acceptsGraphIso
    (source (graph core220) (root 9) 0 0) SmallGeFourSpectrum195.graph
      sourceMap220=true := by decide +kernel
theorem fusedMap220_checked : acceptsGraphIso
    (fused (graph core220) (root 9) 0 0) SmallGeFourSpectrum194.graph
      fusedMap220=true := by decide +kernel
theorem certified220 : Certified (graph core220) (root 9) 0 0 :=
  of_native_maps core220 SmallGeFourSpectrum195.graph SmallGeFourSpectrum194.graph
    sourceMap220 fusedMap220 sourceMap220_checked fusedMap220_checked
    SmallGeFourComparisons.comparison220
#print axioms sourceMap220_checked
#print axioms fusedMap220_checked
#print axioms certified220
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
