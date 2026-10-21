/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core128 : Family 8 := level8.get ⟨239,by decide⟩
def sourceMap128 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap128 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap128_checked : acceptsGraphIso
    (source (graph core128) (root 8) 0 0) SmallGeFourSpectrum078.graph
      sourceMap128=true := by decide +kernel
theorem fusedMap128_checked : acceptsGraphIso
    (fused (graph core128) (root 8) 0 0) SmallGeFourSpectrum059.graph
      fusedMap128=true := by decide +kernel
theorem certified128 : Certified (graph core128) (root 8) 0 0 :=
  of_native_maps core128 SmallGeFourSpectrum078.graph SmallGeFourSpectrum059.graph
    sourceMap128 fusedMap128 sourceMap128_checked fusedMap128_checked
    SmallGeFourComparisons.comparison128
#print axioms sourceMap128_checked
#print axioms fusedMap128_checked
#print axioms certified128
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
