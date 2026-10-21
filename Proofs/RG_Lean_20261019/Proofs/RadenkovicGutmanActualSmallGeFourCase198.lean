/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons11
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core198 : Family 9 := level9.get ⟨583,by decide⟩
def sourceMap198 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap198 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap198_checked : acceptsGraphIso
    (source (graph core198) (root 9) 0 0) SmallGeFourSpectrum136.graph
      sourceMap198=true := by decide +kernel
theorem fusedMap198_checked : acceptsGraphIso
    (fused (graph core198) (root 9) 0 0) SmallGeFourSpectrum135.graph
      fusedMap198=true := by decide +kernel
theorem certified198 : Certified (graph core198) (root 9) 0 0 :=
  of_native_maps core198 SmallGeFourSpectrum136.graph SmallGeFourSpectrum135.graph
    sourceMap198 fusedMap198 sourceMap198_checked fusedMap198_checked
    SmallGeFourComparisons.comparison198
#print axioms sourceMap198_checked
#print axioms fusedMap198_checked
#print axioms certified198
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
