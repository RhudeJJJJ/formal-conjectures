/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons13
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core231 : Family 9 := level9.get ⟨700,by decide⟩
def sourceMap231 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap231 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap231_checked : acceptsGraphIso
    (source (graph core231) (root 9) 0 0) SmallGeFourSpectrum203.graph
      sourceMap231=true := by decide +kernel
theorem fusedMap231_checked : acceptsGraphIso
    (fused (graph core231) (root 9) 0 0) SmallGeFourSpectrum216.graph
      fusedMap231=true := by decide +kernel
theorem certified231 : Certified (graph core231) (root 9) 0 0 :=
  of_native_maps core231 SmallGeFourSpectrum203.graph SmallGeFourSpectrum216.graph
    sourceMap231 fusedMap231 sourceMap231_checked fusedMap231_checked
    SmallGeFourComparisons.comparison231
#print axioms sourceMap231_checked
#print axioms fusedMap231_checked
#print axioms certified231
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
