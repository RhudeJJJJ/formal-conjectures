/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons08
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core138 : Family 8 := level8.get ⟨260,by decide⟩
def sourceMap138 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap138 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,8,9,10,1,2,3,6,7,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap138_checked : acceptsGraphIso
    (source (graph core138) (root 8) 0 0) SmallGeFourSpectrum048.graph
      sourceMap138=true := by decide +kernel
theorem fusedMap138_checked : acceptsGraphIso
    (fused (graph core138) (root 8) 0 0) SmallGeFourSpectrum047.graph
      fusedMap138=true := by decide +kernel
theorem certified138 : Certified (graph core138) (root 8) 0 0 :=
  of_native_maps core138 SmallGeFourSpectrum048.graph SmallGeFourSpectrum047.graph
    sourceMap138 fusedMap138 sourceMap138_checked fusedMap138_checked
    SmallGeFourComparisons.comparison138
#print axioms sourceMap138_checked
#print axioms fusedMap138_checked
#print axioms certified138
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
