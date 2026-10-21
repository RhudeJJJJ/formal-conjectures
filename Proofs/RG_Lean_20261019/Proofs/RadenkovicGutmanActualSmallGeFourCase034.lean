/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons02
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core034 : Family 6 := level6.get ⟨36,by decide⟩
def sourceMap034 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,8,9,10,5,6,7,1,2,3,4] (sourceLabel 6 1 1 v)
def fusedMap034 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap034_checked : acceptsGraphIso
    (source (graph core034) (root 6) 1 1) SmallGeFourSpectrum056.graph
      sourceMap034=true := by decide +kernel
theorem fusedMap034_checked : acceptsGraphIso
    (fused (graph core034) (root 6) 1 1) SmallGeFourSpectrum039.graph
      fusedMap034=true := by decide +kernel
theorem certified034 : Certified (graph core034) (root 6) 1 1 :=
  of_native_maps core034 SmallGeFourSpectrum056.graph SmallGeFourSpectrum039.graph
    sourceMap034 fusedMap034 sourceMap034_checked fusedMap034_checked
    SmallGeFourComparisons.comparison034
#print axioms sourceMap034_checked
#print axioms fusedMap034_checked
#print axioms certified034
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
