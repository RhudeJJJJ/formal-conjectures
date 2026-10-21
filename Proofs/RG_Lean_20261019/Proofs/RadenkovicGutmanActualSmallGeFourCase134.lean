/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core134 : Family 8 := level8.get ⟨254,by decide⟩
def sourceMap134 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,2,3,4,5,6,7] (sourceLabel 8 0 0 v)
def fusedMap134 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,7,8,9,10,3,4,5,6,1,2] (fusedLabel 8 0 0 v)
theorem sourceMap134_checked : acceptsGraphIso
    (source (graph core134) (root 8) 0 0) SmallGeFourSpectrum074.graph
      sourceMap134=true := by decide +kernel
theorem fusedMap134_checked : acceptsGraphIso
    (fused (graph core134) (root 8) 0 0) SmallGeFourSpectrum061.graph
      fusedMap134=true := by decide +kernel
theorem certified134 : Certified (graph core134) (root 8) 0 0 :=
  of_native_maps core134 SmallGeFourSpectrum074.graph SmallGeFourSpectrum061.graph
    sourceMap134 fusedMap134 sourceMap134_checked fusedMap134_checked
    SmallGeFourComparisons.comparison134
#print axioms sourceMap134_checked
#print axioms fusedMap134_checked
#print axioms certified134
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
