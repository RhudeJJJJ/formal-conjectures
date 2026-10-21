/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core122 : Family 8 := level8.get ⟨221,by decide⟩
def sourceMap122 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap122 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap122_checked : acceptsGraphIso
    (source (graph core122) (root 8) 0 0) SmallGeFourSpectrum077.graph
      sourceMap122=true := by decide +kernel
theorem fusedMap122_checked : acceptsGraphIso
    (fused (graph core122) (root 8) 0 0) SmallGeFourSpectrum050.graph
      fusedMap122=true := by decide +kernel
theorem certified122 : Certified (graph core122) (root 8) 0 0 :=
  of_native_maps core122 SmallGeFourSpectrum077.graph SmallGeFourSpectrum050.graph
    sourceMap122 fusedMap122 sourceMap122_checked fusedMap122_checked
    SmallGeFourComparisons.comparison122
#print axioms sourceMap122_checked
#print axioms fusedMap122_checked
#print axioms certified122
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
