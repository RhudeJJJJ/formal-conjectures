/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core183 : Family 9 := level9.get ⟨457,by decide⟩
def sourceMap183 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap183 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap183_checked : acceptsGraphIso
    (source (graph core183) (root 9) 0 0) SmallGeFourSpectrum126.graph
      sourceMap183=true := by decide +kernel
theorem fusedMap183_checked : acceptsGraphIso
    (fused (graph core183) (root 9) 0 0) SmallGeFourSpectrum185.graph
      fusedMap183=true := by decide +kernel
theorem certified183 : Certified (graph core183) (root 9) 0 0 :=
  of_native_maps core183 SmallGeFourSpectrum126.graph SmallGeFourSpectrum185.graph
    sourceMap183 fusedMap183 sourceMap183_checked fusedMap183_checked
    SmallGeFourComparisons.comparison183
#print axioms sourceMap183_checked
#print axioms fusedMap183_checked
#print axioms certified183
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
