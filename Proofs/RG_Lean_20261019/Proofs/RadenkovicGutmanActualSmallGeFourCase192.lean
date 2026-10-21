/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core192 : Family 9 := level9.get ⟨538,by decide⟩
def sourceMap192 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap192 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,7,8,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap192_checked : acceptsGraphIso
    (source (graph core192) (root 9) 0 0) SmallGeFourSpectrum149.graph
      sourceMap192=true := by decide +kernel
theorem fusedMap192_checked : acceptsGraphIso
    (fused (graph core192) (root 9) 0 0) SmallGeFourSpectrum144.graph
      fusedMap192=true := by decide +kernel
theorem certified192 : Certified (graph core192) (root 9) 0 0 :=
  of_native_maps core192 SmallGeFourSpectrum149.graph SmallGeFourSpectrum144.graph
    sourceMap192 fusedMap192 sourceMap192_checked fusedMap192_checked
    SmallGeFourComparisons.comparison192
#print axioms sourceMap192_checked
#print axioms fusedMap192_checked
#print axioms certified192
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
