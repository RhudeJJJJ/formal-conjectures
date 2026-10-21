/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core197 : Family 9 := level9.get ⟨576,by decide⟩
def sourceMap197 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap197 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap197_checked : acceptsGraphIso
    (source (graph core197) (root 9) 0 0) SmallGeFourSpectrum210.graph
      sourceMap197=true := by decide +kernel
theorem fusedMap197_checked : acceptsGraphIso
    (fused (graph core197) (root 9) 0 0) SmallGeFourSpectrum134.graph
      fusedMap197=true := by decide +kernel
theorem certified197 : Certified (graph core197) (root 9) 0 0 :=
  of_native_maps core197 SmallGeFourSpectrum210.graph SmallGeFourSpectrum134.graph
    sourceMap197 fusedMap197 sourceMap197_checked fusedMap197_checked
    SmallGeFourComparisons.comparison197
#print axioms sourceMap197_checked
#print axioms fusedMap197_checked
#print axioms certified197
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
