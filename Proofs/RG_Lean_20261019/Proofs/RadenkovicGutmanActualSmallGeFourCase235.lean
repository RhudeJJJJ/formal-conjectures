/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core235 : Family 9 := level9.get ⟨706,by decide⟩
def sourceMap235 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap235 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,7,8,9,10,11,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap235_checked : acceptsGraphIso
    (source (graph core235) (root 9) 0 0) SmallGeFourSpectrum200.graph
      sourceMap235=true := by decide +kernel
theorem fusedMap235_checked : acceptsGraphIso
    (fused (graph core235) (root 9) 0 0) SmallGeFourSpectrum221.graph
      fusedMap235=true := by decide +kernel
theorem certified235 : Certified (graph core235) (root 9) 0 0 :=
  of_native_maps core235 SmallGeFourSpectrum200.graph SmallGeFourSpectrum221.graph
    sourceMap235 fusedMap235 sourceMap235_checked fusedMap235_checked
    SmallGeFourComparisons.comparison235
#print axioms sourceMap235_checked
#print axioms fusedMap235_checked
#print axioms certified235
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
