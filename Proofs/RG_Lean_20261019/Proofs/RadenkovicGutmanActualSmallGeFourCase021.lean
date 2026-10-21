/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core021 : Family 5 := level5.get ⟨19,by decide⟩
def sourceMap021 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 5 0 0 v)
def fusedMap021 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 5 0 0 v)
theorem sourceMap021_checked : acceptsGraphIso
    (source (graph core021) (root 5) 0 0) SmallGeFourSpectrum005.graph
      sourceMap021=true := by decide +kernel
theorem fusedMap021_checked : acceptsGraphIso
    (fused (graph core021) (root 5) 0 0) SmallGeFourSpectrum002.graph
      fusedMap021=true := by decide +kernel
theorem certified021 : Certified (graph core021) (root 5) 0 0 :=
  of_native_maps core021 SmallGeFourSpectrum005.graph SmallGeFourSpectrum002.graph
    sourceMap021 fusedMap021 sourceMap021_checked fusedMap021_checked
    SmallGeFourComparisons.comparison021
#print axioms sourceMap021_checked
#print axioms fusedMap021_checked
#print axioms certified021
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
