/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core079 : Family 7 := level7.get ⟨99,by decide⟩
def sourceMap079 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,5,6,7,8,1,2,3,4] (sourceLabel 7 1 1 v)
def fusedMap079 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap079_checked : acceptsGraphIso
    (source (graph core079) (root 7) 1 1) SmallGeFourSpectrum167.graph
      sourceMap079=true := by decide +kernel
theorem fusedMap079_checked : acceptsGraphIso
    (fused (graph core079) (root 7) 1 1) SmallGeFourSpectrum108.graph
      fusedMap079=true := by decide +kernel
theorem certified079 : Certified (graph core079) (root 7) 1 1 :=
  of_native_maps core079 SmallGeFourSpectrum167.graph SmallGeFourSpectrum108.graph
    sourceMap079 fusedMap079 sourceMap079_checked fusedMap079_checked
    SmallGeFourComparisons.comparison079
#print axioms sourceMap079_checked
#print axioms fusedMap079_checked
#print axioms certified079
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
