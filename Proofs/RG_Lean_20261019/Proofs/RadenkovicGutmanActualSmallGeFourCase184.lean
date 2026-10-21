/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core184 : Family 9 := level9.get ⟨476,by decide⟩
def sourceMap184 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,7,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap184 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap184_checked : acceptsGraphIso
    (source (graph core184) (root 9) 0 0) SmallGeFourSpectrum120.graph
      sourceMap184=true := by decide +kernel
theorem fusedMap184_checked : acceptsGraphIso
    (fused (graph core184) (root 9) 0 0) SmallGeFourSpectrum186.graph
      fusedMap184=true := by decide +kernel
theorem certified184 : Certified (graph core184) (root 9) 0 0 :=
  of_native_maps core184 SmallGeFourSpectrum120.graph SmallGeFourSpectrum186.graph
    sourceMap184 fusedMap184 sourceMap184_checked fusedMap184_checked
    SmallGeFourComparisons.comparison184
#print axioms sourceMap184_checked
#print axioms fusedMap184_checked
#print axioms certified184
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
