/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core160 : Family 8 := level8.get ⟨281,by decide⟩
def sourceMap160 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap160 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap160_checked : acceptsGraphIso
    (source (graph core160) (root 8) 0 0) SmallGeFourSpectrum089.graph
      sourceMap160=true := by decide +kernel
theorem fusedMap160_checked : acceptsGraphIso
    (fused (graph core160) (root 8) 0 0) SmallGeFourSpectrum088.graph
      fusedMap160=true := by decide +kernel
theorem certified160 : Certified (graph core160) (root 8) 0 0 :=
  of_native_maps core160 SmallGeFourSpectrum089.graph SmallGeFourSpectrum088.graph
    sourceMap160 fusedMap160 sourceMap160_checked fusedMap160_checked
    SmallGeFourComparisons.comparison160
#print axioms sourceMap160_checked
#print axioms fusedMap160_checked
#print axioms certified160
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
