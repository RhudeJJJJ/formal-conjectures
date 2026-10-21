/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core229 : Family 9 := level9.get ⟨695,by decide⟩
def sourceMap229 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap229 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap229_checked : acceptsGraphIso
    (source (graph core229) (root 9) 0 0) SmallGeFourSpectrum208.graph
      sourceMap229=true := by decide +kernel
theorem fusedMap229_checked : acceptsGraphIso
    (fused (graph core229) (root 9) 0 0) SmallGeFourSpectrum214.graph
      fusedMap229=true := by decide +kernel
theorem certified229 : Certified (graph core229) (root 9) 0 0 :=
  of_native_maps core229 SmallGeFourSpectrum208.graph SmallGeFourSpectrum214.graph
    sourceMap229 fusedMap229 sourceMap229_checked fusedMap229_checked
    SmallGeFourComparisons.comparison229
#print axioms sourceMap229_checked
#print axioms fusedMap229_checked
#print axioms certified229
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
