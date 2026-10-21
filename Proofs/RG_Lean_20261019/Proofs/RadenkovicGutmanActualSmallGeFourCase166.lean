/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core166 : Family 8 := level8.get ⟨284,by decide⟩
def sourceMap166 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,9,10,1,2,3,4,5,6,7,8] (sourceLabel 8 0 0 v)
def fusedMap166 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,5,6,7,8,9,10,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap166_checked : acceptsGraphIso
    (source (graph core166) (root 8) 0 0) SmallGeFourSpectrum069.graph
      sourceMap166=true := by decide +kernel
theorem fusedMap166_checked : acceptsGraphIso
    (fused (graph core166) (root 8) 0 0) SmallGeFourSpectrum091.graph
      fusedMap166=true := by decide +kernel
theorem certified166 : Certified (graph core166) (root 8) 0 0 :=
  of_native_maps core166 SmallGeFourSpectrum069.graph SmallGeFourSpectrum091.graph
    sourceMap166 fusedMap166 sourceMap166_checked fusedMap166_checked
    SmallGeFourComparisons.comparison166
#print axioms sourceMap166_checked
#print axioms fusedMap166_checked
#print axioms certified166
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
