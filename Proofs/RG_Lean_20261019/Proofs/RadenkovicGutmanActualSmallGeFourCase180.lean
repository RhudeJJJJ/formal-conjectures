/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core180 : Family 9 := level9.get ⟨413,by decide⟩
def sourceMap180 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap180 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap180_checked : acceptsGraphIso
    (source (graph core180) (root 9) 0 0) SmallGeFourSpectrum159.graph
      sourceMap180=true := by decide +kernel
theorem fusedMap180_checked : acceptsGraphIso
    (fused (graph core180) (root 9) 0 0) SmallGeFourSpectrum157.graph
      fusedMap180=true := by decide +kernel
theorem certified180 : Certified (graph core180) (root 9) 0 0 :=
  of_native_maps core180 SmallGeFourSpectrum159.graph SmallGeFourSpectrum157.graph
    sourceMap180 fusedMap180 sourceMap180_checked fusedMap180_checked
    SmallGeFourComparisons.comparison180
#print axioms sourceMap180_checked
#print axioms fusedMap180_checked
#print axioms certified180
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
