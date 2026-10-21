/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core238 : Family 9 := level9.get ⟨710,by decide⟩
def sourceMap238 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap238 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap238_checked : acceptsGraphIso
    (source (graph core238) (root 9) 0 0) SmallGeFourSpectrum226.graph
      sourceMap238=true := by decide +kernel
theorem fusedMap238_checked : acceptsGraphIso
    (fused (graph core238) (root 9) 0 0) SmallGeFourSpectrum225.graph
      fusedMap238=true := by decide +kernel
theorem certified238 : Certified (graph core238) (root 9) 0 0 :=
  of_native_maps core238 SmallGeFourSpectrum226.graph SmallGeFourSpectrum225.graph
    sourceMap238 fusedMap238 sourceMap238_checked fusedMap238_checked
    SmallGeFourComparisons.comparison238
#print axioms sourceMap238_checked
#print axioms fusedMap238_checked
#print axioms certified238
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
