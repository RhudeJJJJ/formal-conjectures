/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core042 : Family 6 := level6.get ⟨45,by decide⟩
def sourceMap042 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 6 0 0 v)
def fusedMap042 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,7,8,5,6] (fusedLabel 6 0 0 v)
theorem sourceMap042_checked : acceptsGraphIso
    (source (graph core042) (root 6) 0 0) SmallGeFourSpectrum013.graph
      sourceMap042=true := by decide +kernel
theorem fusedMap042_checked : acceptsGraphIso
    (fused (graph core042) (root 6) 0 0) SmallGeFourSpectrum012.graph
      fusedMap042=true := by decide +kernel
theorem certified042 : Certified (graph core042) (root 6) 0 0 :=
  of_native_maps core042 SmallGeFourSpectrum013.graph SmallGeFourSpectrum012.graph
    sourceMap042 fusedMap042 sourceMap042_checked fusedMap042_checked
    SmallGeFourComparisons.comparison042
#print axioms sourceMap042_checked
#print axioms fusedMap042_checked
#print axioms certified042
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
