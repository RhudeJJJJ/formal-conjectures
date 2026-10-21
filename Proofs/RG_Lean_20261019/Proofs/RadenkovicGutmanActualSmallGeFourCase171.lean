/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons10
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core171 : Family 9 := level9.get ⟨198,by decide⟩
def sourceMap171 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap171 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap171_checked : acceptsGraphIso
    (source (graph core171) (root 9) 0 0) SmallGeFourSpectrum124.graph
      sourceMap171=true := by decide +kernel
theorem fusedMap171_checked : acceptsGraphIso
    (fused (graph core171) (root 9) 0 0) SmallGeFourSpectrum097.graph
      fusedMap171=true := by decide +kernel
theorem certified171 : Certified (graph core171) (root 9) 0 0 :=
  of_native_maps core171 SmallGeFourSpectrum124.graph SmallGeFourSpectrum097.graph
    sourceMap171 fusedMap171 sourceMap171_checked fusedMap171_checked
    SmallGeFourComparisons.comparison171
#print axioms sourceMap171_checked
#print axioms fusedMap171_checked
#print axioms certified171
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
