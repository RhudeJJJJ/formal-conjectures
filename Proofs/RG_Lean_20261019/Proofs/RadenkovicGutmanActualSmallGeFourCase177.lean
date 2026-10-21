/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core177 : Family 9 := level9.get ⟨353,by decide⟩
def sourceMap177 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap177 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap177_checked : acceptsGraphIso
    (source (graph core177) (root 9) 0 0) SmallGeFourSpectrum122.graph
      sourceMap177=true := by decide +kernel
theorem fusedMap177_checked : acceptsGraphIso
    (fused (graph core177) (root 9) 0 0) SmallGeFourSpectrum137.graph
      fusedMap177=true := by decide +kernel
theorem certified177 : Certified (graph core177) (root 9) 0 0 :=
  of_native_maps core177 SmallGeFourSpectrum122.graph SmallGeFourSpectrum137.graph
    sourceMap177 fusedMap177 sourceMap177_checked fusedMap177_checked
    SmallGeFourComparisons.comparison177
#print axioms sourceMap177_checked
#print axioms fusedMap177_checked
#print axioms certified177
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
