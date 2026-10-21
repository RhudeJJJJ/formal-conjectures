/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core208 : Family 9 := level9.get ⟨628,by decide⟩
def sourceMap208 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap208 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![4,0,1,2,3,7,8,9,10,11,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap208_checked : acceptsGraphIso
    (source (graph core208) (root 9) 0 0) SmallGeFourSpectrum201.graph
      sourceMap208=true := by decide +kernel
theorem fusedMap208_checked : acceptsGraphIso
    (fused (graph core208) (root 9) 0 0) SmallGeFourSpectrum158.graph
      fusedMap208=true := by decide +kernel
theorem certified208 : Certified (graph core208) (root 9) 0 0 :=
  of_native_maps core208 SmallGeFourSpectrum201.graph SmallGeFourSpectrum158.graph
    sourceMap208 fusedMap208 sourceMap208_checked fusedMap208_checked
    SmallGeFourComparisons.comparison208
#print axioms sourceMap208_checked
#print axioms fusedMap208_checked
#print axioms certified208
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
