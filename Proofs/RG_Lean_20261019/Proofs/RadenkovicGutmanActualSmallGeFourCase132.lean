/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core132 : Family 8 := level8.get ⟨253,by decide⟩
def sourceMap132 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap132 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,5,6,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap132_checked : acceptsGraphIso
    (source (graph core132) (root 8) 0 0) SmallGeFourSpectrum061.graph
      sourceMap132=true := by decide +kernel
theorem fusedMap132_checked : acceptsGraphIso
    (fused (graph core132) (root 8) 0 0) SmallGeFourSpectrum057.graph
      fusedMap132=true := by decide +kernel
theorem certified132 : Certified (graph core132) (root 8) 0 0 :=
  of_native_maps core132 SmallGeFourSpectrum061.graph SmallGeFourSpectrum057.graph
    sourceMap132 fusedMap132 sourceMap132_checked fusedMap132_checked
    SmallGeFourComparisons.comparison132
#print axioms sourceMap132_checked
#print axioms fusedMap132_checked
#print axioms certified132
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
