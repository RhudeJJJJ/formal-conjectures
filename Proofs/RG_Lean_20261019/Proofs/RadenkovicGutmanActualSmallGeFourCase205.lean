/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core205 : Family 9 := level9.get ⟨625,by decide⟩
def sourceMap205 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap205 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,6,7,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap205_checked : acceptsGraphIso
    (source (graph core205) (root 9) 0 0) SmallGeFourSpectrum147.graph
      sourceMap205=true := by decide +kernel
theorem fusedMap205_checked : acceptsGraphIso
    (fused (graph core205) (root 9) 0 0) SmallGeFourSpectrum142.graph
      fusedMap205=true := by decide +kernel
theorem certified205 : Certified (graph core205) (root 9) 0 0 :=
  of_native_maps core205 SmallGeFourSpectrum147.graph SmallGeFourSpectrum142.graph
    sourceMap205 fusedMap205 sourceMap205_checked fusedMap205_checked
    SmallGeFourComparisons.comparison205
#print axioms sourceMap205_checked
#print axioms fusedMap205_checked
#print axioms certified205
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
