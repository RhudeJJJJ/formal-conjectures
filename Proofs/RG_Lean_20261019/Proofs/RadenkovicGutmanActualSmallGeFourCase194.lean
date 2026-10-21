/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core194 : Family 9 := level9.get ⟨540,by decide⟩
def sourceMap194 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap194 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,6,7,8,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap194_checked : acceptsGraphIso
    (source (graph core194) (root 9) 0 0) SmallGeFourSpectrum180.graph
      sourceMap194=true := by decide +kernel
theorem fusedMap194_checked : acceptsGraphIso
    (fused (graph core194) (root 9) 0 0) SmallGeFourSpectrum169.graph
      fusedMap194=true := by decide +kernel
theorem certified194 : Certified (graph core194) (root 9) 0 0 :=
  of_native_maps core194 SmallGeFourSpectrum180.graph SmallGeFourSpectrum169.graph
    sourceMap194 fusedMap194 sourceMap194_checked fusedMap194_checked
    SmallGeFourComparisons.comparison194
#print axioms sourceMap194_checked
#print axioms fusedMap194_checked
#print axioms certified194
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
