/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core006 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap006 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,5,6,7,8,1,2,3,4] (sourceLabel 4 1 1 v)
def fusedMap006 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 1 1 v)
theorem sourceMap006_checked : acceptsGraphIso
    (source (graph core006) (root 4) 1 1) SmallGeFourSpectrum013.graph
      sourceMap006=true := by decide +kernel
theorem fusedMap006_checked : acceptsGraphIso
    (fused (graph core006) (root 4) 1 1) SmallGeFourSpectrum006.graph
      fusedMap006=true := by decide +kernel
theorem certified006 : Certified (graph core006) (root 4) 1 1 :=
  of_native_maps core006 SmallGeFourSpectrum013.graph SmallGeFourSpectrum006.graph
    sourceMap006 fusedMap006 sourceMap006_checked fusedMap006_checked
    SmallGeFourComparisons.comparison006
#print axioms sourceMap006_checked
#print axioms fusedMap006_checked
#print axioms certified006
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
