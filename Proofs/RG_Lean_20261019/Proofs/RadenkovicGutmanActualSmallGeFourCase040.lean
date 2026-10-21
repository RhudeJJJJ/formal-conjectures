/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core040 : Family 6 := level6.get ⟨43,by decide⟩
def sourceMap040 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,8,9,10,4,5,6,7] (sourceLabel 6 1 1 v)
def fusedMap040 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap040_checked : acceptsGraphIso
    (source (graph core040) (root 6) 1 1) SmallGeFourSpectrum086.graph
      sourceMap040=true := by decide +kernel
theorem fusedMap040_checked : acceptsGraphIso
    (fused (graph core040) (root 6) 1 1) SmallGeFourSpectrum049.graph
      fusedMap040=true := by decide +kernel
theorem certified040 : Certified (graph core040) (root 6) 1 1 :=
  of_native_maps core040 SmallGeFourSpectrum086.graph SmallGeFourSpectrum049.graph
    sourceMap040 fusedMap040 sourceMap040_checked fusedMap040_checked
    SmallGeFourComparisons.comparison040
#print axioms sourceMap040_checked
#print axioms fusedMap040_checked
#print axioms certified040
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
