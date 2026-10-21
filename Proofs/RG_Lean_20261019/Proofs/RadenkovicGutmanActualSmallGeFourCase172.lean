/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core172 : Family 9 := level9.get ⟨250,by decide⟩
def sourceMap172 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap172 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap172_checked : acceptsGraphIso
    (source (graph core172) (root 9) 0 0) SmallGeFourSpectrum127.graph
      sourceMap172=true := by decide +kernel
theorem fusedMap172_checked : acceptsGraphIso
    (fused (graph core172) (root 9) 0 0) SmallGeFourSpectrum102.graph
      fusedMap172=true := by decide +kernel
theorem certified172 : Certified (graph core172) (root 9) 0 0 :=
  of_native_maps core172 SmallGeFourSpectrum127.graph SmallGeFourSpectrum102.graph
    sourceMap172 fusedMap172 sourceMap172_checked fusedMap172_checked
    SmallGeFourComparisons.comparison172
#print axioms sourceMap172_checked
#print axioms fusedMap172_checked
#print axioms certified172
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
