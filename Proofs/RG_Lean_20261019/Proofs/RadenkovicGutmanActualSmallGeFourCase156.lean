/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core156 : Family 8 := level8.get ⟨279,by decide⟩
def sourceMap156 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap156 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap156_checked : acceptsGraphIso
    (source (graph core156) (root 8) 0 0) SmallGeFourSpectrum087.graph
      sourceMap156=true := by decide +kernel
theorem fusedMap156_checked : acceptsGraphIso
    (fused (graph core156) (root 8) 0 0) SmallGeFourSpectrum086.graph
      fusedMap156=true := by decide +kernel
theorem certified156 : Certified (graph core156) (root 8) 0 0 :=
  of_native_maps core156 SmallGeFourSpectrum087.graph SmallGeFourSpectrum086.graph
    sourceMap156 fusedMap156 sourceMap156_checked fusedMap156_checked
    SmallGeFourComparisons.comparison156
#print axioms sourceMap156_checked
#print axioms fusedMap156_checked
#print axioms certified156
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
