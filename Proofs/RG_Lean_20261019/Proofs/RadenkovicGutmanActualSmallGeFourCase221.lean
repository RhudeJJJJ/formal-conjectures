/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core221 : Family 9 := level9.get ⟨677,by decide⟩
def sourceMap221 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap221 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap221_checked : acceptsGraphIso
    (source (graph core221) (root 9) 0 0) SmallGeFourSpectrum196.graph
      sourceMap221=true := by decide +kernel
theorem fusedMap221_checked : acceptsGraphIso
    (fused (graph core221) (root 9) 0 0) SmallGeFourSpectrum195.graph
      fusedMap221=true := by decide +kernel
theorem certified221 : Certified (graph core221) (root 9) 0 0 :=
  of_native_maps core221 SmallGeFourSpectrum196.graph SmallGeFourSpectrum195.graph
    sourceMap221 fusedMap221 sourceMap221_checked fusedMap221_checked
    SmallGeFourComparisons.comparison221
#print axioms sourceMap221_checked
#print axioms fusedMap221_checked
#print axioms certified221
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
