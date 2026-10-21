/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core046 : Family 6 := level6.get ⟨45,by decide⟩
def sourceMap046 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,9,10,5,6,7,8] (sourceLabel 6 1 1 v)
def fusedMap046 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap046_checked : acceptsGraphIso
    (source (graph core046) (root 6) 1 1) SmallGeFourSpectrum089.graph
      sourceMap046=true := by decide +kernel
theorem fusedMap046_checked : acceptsGraphIso
    (fused (graph core046) (root 6) 1 1) SmallGeFourSpectrum058.graph
      fusedMap046=true := by decide +kernel
theorem certified046 : Certified (graph core046) (root 6) 1 1 :=
  of_native_maps core046 SmallGeFourSpectrum089.graph SmallGeFourSpectrum058.graph
    sourceMap046 fusedMap046 sourceMap046_checked fusedMap046_checked
    SmallGeFourComparisons.comparison046
#print axioms sourceMap046_checked
#print axioms fusedMap046_checked
#print axioms certified046
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
