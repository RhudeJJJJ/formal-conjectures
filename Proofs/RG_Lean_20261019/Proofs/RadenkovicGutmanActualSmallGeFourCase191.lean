/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core191 : Family 9 := level9.get ⟨534,by decide⟩
def sourceMap191 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap191 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,8,9,10,11,1,2,3,6,7,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap191_checked : acceptsGraphIso
    (source (graph core191) (root 9) 0 0) SmallGeFourSpectrum108.graph
      sourceMap191=true := by decide +kernel
theorem fusedMap191_checked : acceptsGraphIso
    (fused (graph core191) (root 9) 0 0) SmallGeFourSpectrum107.graph
      fusedMap191=true := by decide +kernel
theorem certified191 : Certified (graph core191) (root 9) 0 0 :=
  of_native_maps core191 SmallGeFourSpectrum108.graph SmallGeFourSpectrum107.graph
    sourceMap191 fusedMap191 sourceMap191_checked fusedMap191_checked
    SmallGeFourComparisons.comparison191
#print axioms sourceMap191_checked
#print axioms fusedMap191_checked
#print axioms certified191
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
