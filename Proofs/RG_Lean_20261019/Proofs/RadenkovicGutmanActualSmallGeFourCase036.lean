/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core036 : Family 6 := level6.get ⟨43,by decide⟩
def sourceMap036 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,6,7,8,1,2,3,4,5] (sourceLabel 6 0 0 v)
def fusedMap036 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,6,7,8,4,5] (fusedLabel 6 0 0 v)
theorem sourceMap036_checked : acceptsGraphIso
    (source (graph core036) (root 6) 0 0) SmallGeFourSpectrum009.graph
      sourceMap036=true := by decide +kernel
theorem fusedMap036_checked : acceptsGraphIso
    (fused (graph core036) (root 6) 0 0) SmallGeFourSpectrum011.graph
      fusedMap036=true := by decide +kernel
theorem certified036 : Certified (graph core036) (root 6) 0 0 :=
  of_native_maps core036 SmallGeFourSpectrum009.graph SmallGeFourSpectrum011.graph
    sourceMap036 fusedMap036 sourceMap036_checked fusedMap036_checked
    SmallGeFourComparisons.comparison036
#print axioms sourceMap036_checked
#print axioms fusedMap036_checked
#print axioms certified036
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
