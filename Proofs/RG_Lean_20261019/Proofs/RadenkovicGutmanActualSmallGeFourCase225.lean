/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core225 : Family 9 := level9.get ⟨685,by decide⟩
def sourceMap225 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap225 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap225_checked : acceptsGraphIso
    (source (graph core225) (root 9) 0 0) SmallGeFourSpectrum164.graph
      sourceMap225=true := by decide +kernel
theorem fusedMap225_checked : acceptsGraphIso
    (fused (graph core225) (root 9) 0 0) SmallGeFourSpectrum163.graph
      fusedMap225=true := by decide +kernel
theorem certified225 : Certified (graph core225) (root 9) 0 0 :=
  of_native_maps core225 SmallGeFourSpectrum164.graph SmallGeFourSpectrum163.graph
    sourceMap225 fusedMap225 sourceMap225_checked fusedMap225_checked
    SmallGeFourComparisons.comparison225
#print axioms sourceMap225_checked
#print axioms fusedMap225_checked
#print axioms certified225
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
