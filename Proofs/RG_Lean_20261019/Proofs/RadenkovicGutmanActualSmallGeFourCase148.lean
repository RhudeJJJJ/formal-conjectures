/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core148 : Family 8 := level8.get ⟨274,by decide⟩
def sourceMap148 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap148 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap148_checked : acceptsGraphIso
    (source (graph core148) (root 8) 0 0) SmallGeFourSpectrum082.graph
      sourceMap148=true := by decide +kernel
theorem fusedMap148_checked : acceptsGraphIso
    (fused (graph core148) (root 8) 0 0) SmallGeFourSpectrum081.graph
      fusedMap148=true := by decide +kernel
theorem certified148 : Certified (graph core148) (root 8) 0 0 :=
  of_native_maps core148 SmallGeFourSpectrum082.graph SmallGeFourSpectrum081.graph
    sourceMap148 fusedMap148 sourceMap148_checked fusedMap148_checked
    SmallGeFourComparisons.comparison148
#print axioms sourceMap148_checked
#print axioms fusedMap148_checked
#print axioms certified148
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
