/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core048 : Family 6 := level6.get ⟨46,by decide⟩
def sourceMap048 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,7,8,1,2,3,4,5,6] (sourceLabel 6 0 0 v)
def fusedMap048 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,5,6,7,8,3,4] (fusedLabel 6 0 0 v)
theorem sourceMap048_checked : acceptsGraphIso
    (source (graph core048) (root 6) 0 0) SmallGeFourSpectrum008.graph
      sourceMap048=true := by decide +kernel
theorem fusedMap048_checked : acceptsGraphIso
    (fused (graph core048) (root 6) 0 0) SmallGeFourSpectrum013.graph
      fusedMap048=true := by decide +kernel
theorem certified048 : Certified (graph core048) (root 6) 0 0 :=
  of_native_maps core048 SmallGeFourSpectrum008.graph SmallGeFourSpectrum013.graph
    sourceMap048 fusedMap048 sourceMap048_checked fusedMap048_checked
    SmallGeFourComparisons.comparison048
#print axioms sourceMap048_checked
#print axioms fusedMap048_checked
#print axioms certified048
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
