/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core020 : Family 5 := level5.get ⟨18,by decide⟩
def sourceMap020 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 5 2 2 v)
def fusedMap020 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap020_checked : acceptsGraphIso
    (source (graph core020) (root 5) 2 2) SmallGeFourSpectrum195.graph
      sourceMap020=true := by decide +kernel
theorem fusedMap020_checked : acceptsGraphIso
    (fused (graph core020) (root 5) 2 2) SmallGeFourSpectrum104.graph
      fusedMap020=true := by decide +kernel
theorem certified020 : Certified (graph core020) (root 5) 2 2 :=
  of_native_maps core020 SmallGeFourSpectrum195.graph SmallGeFourSpectrum104.graph
    sourceMap020 fusedMap020 sourceMap020_checked fusedMap020_checked
    SmallGeFourComparisons.comparison020
#print axioms sourceMap020_checked
#print axioms fusedMap020_checked
#print axioms certified020
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
