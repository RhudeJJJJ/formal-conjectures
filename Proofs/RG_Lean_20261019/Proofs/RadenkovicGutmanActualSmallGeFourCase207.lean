/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons12
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core207 : Family 9 := level9.get ⟨627,by decide⟩
def sourceMap207 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![4,0,1,2,3,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap207 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![4,0,1,2,3,5,6,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap207_checked : acceptsGraphIso
    (source (graph core207) (root 9) 0 0) SmallGeFourSpectrum158.graph
      sourceMap207=true := by decide +kernel
theorem fusedMap207_checked : acceptsGraphIso
    (fused (graph core207) (root 9) 0 0) SmallGeFourSpectrum156.graph
      fusedMap207=true := by decide +kernel
theorem certified207 : Certified (graph core207) (root 9) 0 0 :=
  of_native_maps core207 SmallGeFourSpectrum158.graph SmallGeFourSpectrum156.graph
    sourceMap207 fusedMap207 sourceMap207_checked fusedMap207_checked
    SmallGeFourComparisons.comparison207
#print axioms sourceMap207_checked
#print axioms fusedMap207_checked
#print axioms certified207
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
